package com.example.spawnerplus;

import net.kyori.adventure.text.Component;
import net.kyori.adventure.text.format.NamedTextColor;
import net.kyori.adventure.text.format.TextDecoration;
import org.bukkit.GameMode;
import org.bukkit.Location;
import org.bukkit.Material;
import org.bukkit.NamespacedKey;
import org.bukkit.World;
import org.bukkit.block.Block;
import org.bukkit.block.BlockFace;
import org.bukkit.block.BlockState;
import org.bukkit.block.CreatureSpawner;
import org.bukkit.command.Command;
import org.bukkit.command.CommandExecutor;
import org.bukkit.command.CommandSender;
import org.bukkit.configuration.ConfigurationSection;
import org.bukkit.configuration.file.FileConfiguration;
import org.bukkit.configuration.file.YamlConfiguration;
import org.bukkit.enchantments.Enchantment;
import org.bukkit.event.Event;
import org.bukkit.entity.Entity;
import org.bukkit.entity.EntityType;
import org.bukkit.entity.LivingEntity;
import org.bukkit.entity.Player;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.Listener;
import org.bukkit.event.block.Action;
import org.bukkit.event.block.BlockBreakEvent;
import org.bukkit.event.block.BlockExplodeEvent;
import org.bukkit.event.entity.CreatureSpawnEvent;
import org.bukkit.event.entity.EntityDeathEvent;
import org.bukkit.event.entity.EntityExplodeEvent;
import org.bukkit.event.entity.SpawnerSpawnEvent;
import org.bukkit.event.inventory.ClickType;
import org.bukkit.event.inventory.InventoryClickEvent;
import org.bukkit.event.inventory.InventoryCloseEvent;
import org.bukkit.event.inventory.InventoryDragEvent;
import org.bukkit.event.player.PlayerInteractEvent;
import org.bukkit.inventory.EntityEquipment;
import org.bukkit.inventory.EquipmentSlot;
import org.bukkit.inventory.Inventory;
import org.bukkit.inventory.InventoryHolder;
import org.bukkit.inventory.ItemStack;
import org.bukkit.inventory.meta.BlockStateMeta;
import org.bukkit.inventory.meta.ItemMeta;
import org.bukkit.persistence.PersistentDataContainer;
import org.bukkit.persistence.PersistentDataType;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.scheduler.BukkitTask;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ThreadLocalRandom;
import java.util.logging.Level;

/**
 * SpawnerPlus - GUI driven spawner overhaul.
 *
 * Single class by design (build spec section 3). Everything runs on the main server
 * thread; the concurrent maps are defensive, not an invitation to touch state
 * off-thread. Folia is explicitly unsupported (spec section 8).
 */
public final class SpawnerPlus extends JavaPlugin implements Listener, CommandExecutor {

    // ---------------------------------------------------------------- constants

    private static final int GUI_SIZE = 27;
    private static final int SLOT_STATUS = 4;
    private static final int SLOT_EGG = 11;
    private static final int SLOT_MULTIPLIER = 13;
    private static final int SLOT_CORE = 15;
    private static final int SLOT_LABEL_EGG = 20;
    private static final int SLOT_LABEL_MULTIPLIER = 22;
    private static final int SLOT_LABEL_CORE = 24;

    private static final int LOOP_PERIOD_TICKS = 10;
    private static final int RECONCILE_EVERY_CYCLES = 60;   // 30s
    private static final int SAVE_PERIOD_TICKS = 100;       // 5s

    private static final int VANILLA_PLAYER_RANGE = 16;
    private static final int VANILLA_DELAY = 200;
    private static final int VANILLA_SPAWN_COUNT = 4;
    private static final int VANILLA_MIN_SPAWN_DELAY = 200;
    private static final int VANILLA_MAX_SPAWN_DELAY = 800;

    /**
     * REQ-3: vanilla persists the spawner delay fields to NBT as shorts.
     * Integer.MAX_VALUE truncates to -1, which vanilla reads as "reset me", so the
     * block quietly resumes spawning after a chunk unload and reload.
     */
    private static final int SUPPRESSED_DELAY = Short.MAX_VALUE;

    /** Safety valve so an absurd multiplier cannot overflow or flood a chunk. */
    private static final long MAX_MERGED_AMOUNT = 100_000L;

    private static final String SUFFIX_SPAWN_EGG = "_SPAWN_EGG";

    // -------------------------------------------------------------------- state

    /** Keyed "world;x;y;z" - see locationKey(Location). */
    private final Map<String, SpawnerData> spawners = new ConcurrentHashMap<>();
    /** Live mobs per spawner key, maintained incrementally (REQ-6a). */
    private final Map<String, Integer> aliveCounts = new ConcurrentHashMap<>();

    private NamespacedKey keyOwner;
    private NamespacedKey keyMultiplier;

    /** Spawner keys already warned about in this reconcile window, to keep the log readable. */
    private final Set<String> reportedFailures = ConcurrentHashMap.newKeySet();

    private File storageFile;
    private volatile boolean dirty;
    private long cycleCounter;

    private BukkitTask tickTask;
    private BukkitTask saveTask;

    // ------------------------------------------------------------------- config

    private int spawnInterval = 120;
    private int boostedInterval = 60;
    private int mobCap = 24;
    private int maxMobsPerCycle = 5;
    private int requiredPlayerRange = 32;
    private boolean multiplyExperience = true;
    private boolean manageAllSpawners = true;
    private boolean dropSpawnerOnBreak = true;
    private boolean requireSilkTouch = false;
    private boolean allowCreativeDrops = true;
    private Material coreItem = Material.HEAVY_CORE;
    private Map<Material, Integer> multipliers = new LinkedHashMap<>();
    private boolean debug = false;

    // -------------------------------------------------------------- inner types

    /** Per-spawner state. Mutated only on the main thread. */
    private static final class SpawnerData {
        ItemStack egg;
        ItemStack multiplierItem;
        ItemStack core;
        int ticksLeft;
        /** Whether managed suppression has been asserted since the last reconcile. */
        boolean applied;
        UUID viewer;
        /** REQ-4: the mob the block spawned before the plugin touched it. */
        EntityType originalType;
        /**
         * Whether originalType has actually been read from the block. A blank spawner
         * (creative-placed, no mob set) legitimately reads back null, which is not the
         * same as "not looked yet" - without this flag the egg's type would stay baked
         * into a blank block forever.
         */
        boolean originalCaptured;
    }

    /** Marks an inventory as one of ours and carries the spawner key. */
    private static final class SpawnerHolder implements InventoryHolder {
        private final String key;
        private Inventory inventory;

        private SpawnerHolder(String key) {
            this.key = key;
        }

        @Override
        public Inventory getInventory() {
            return inventory;
        }
    }

    // --------------------------------------------------------- plugin lifecycle

    @Override
    public void onEnable() {
        if (isFolia()) {
            getLogger().severe("Folia detected. SpawnerPlus uses the global scheduler and is not Folia compatible.");
            getLogger().severe("Disabling cleanly instead of crashing on startup. Run this plugin on Paper.");
            getServer().getPluginManager().disablePlugin(this);
            return;
        }

        keyOwner = new NamespacedKey(this, "owner");
        keyMultiplier = new NamespacedKey(this, "multiplier");

        saveDefaultConfig();
        loadSettings();

        storageFile = new File(getDataFolder(), "spawners.yml");
        loadStorage();

        getServer().getPluginManager().registerEvents(this, this);
        if (getCommand("spawnerplus") != null) {
            getCommand("spawnerplus").setExecutor(this);
        }

        tickTask = getServer().getScheduler().runTaskTimer(this, this::tick, LOOP_PERIOD_TICKS, LOOP_PERIOD_TICKS);
        saveTask = getServer().getScheduler().runTaskTimer(this, () -> {
            if (dirty) {
                saveStorage();
            }
        }, SAVE_PERIOD_TICKS, SAVE_PERIOD_TICKS);

        getLogger().info("Enabled. Tracking " + spawners.size() + " spawner(s). manage-all-spawners="
                + manageAllSpawners + ", debug=" + debug);
    }

    @Override
    public void onDisable() {
        if (tickTask != null) {
            tickTask.cancel();
        }
        if (saveTask != null) {
            saveTask.cancel();
        }

        // Close open GUIs first so their contents are synced back into SpawnerData
        // before the final save.
        for (Player player : new ArrayList<>(getServer().getOnlinePlayers())) {
            if (player.getOpenInventory().getTopInventory().getHolder() instanceof SpawnerHolder) {
                player.closeInventory();
            }
        }

        releaseAllToVanilla();

        if (storageFile != null) {
            saveStorage();   // REQ-6b: forced synchronous flush on shutdown
        }
    }

    private static boolean isFolia() {
        try {
            Class.forName("io.papermc.paper.threadedregions.RegionizedServer");
            return true;
        } catch (ClassNotFoundException ignored) {
            return false;
        }
    }

    // ------------------------------------------------------------------ settings

    private void loadSettings() {
        FileConfiguration config = getConfig();

        spawnInterval = roundToPeriod(config.getInt("spawn-interval-ticks", 120));
        boostedInterval = roundToPeriod(config.getInt("boosted-interval-ticks", 60));
        mobCap = Math.max(1, config.getInt("mob-cap", 24));
        maxMobsPerCycle = Math.max(1, config.getInt("max-mobs-per-cycle", 5));
        requiredPlayerRange = Math.max(0, config.getInt("required-player-range", 32));
        multiplyExperience = config.getBoolean("multiply-experience", true);
        manageAllSpawners = config.getBoolean("manage-all-spawners", true);
        dropSpawnerOnBreak = config.getBoolean("drop-spawner-on-break", true);
        requireSilkTouch = config.getBoolean("require-silk-touch", false);
        allowCreativeDrops = config.getBoolean("allow-creative-drops", true);
        debug = config.getBoolean("debug", false);

        String coreName = config.getString("core-item", "HEAVY_CORE");
        Material core = Material.matchMaterial(coreName == null ? "" : coreName);
        if (core == null) {
            getLogger().warning("core-item " + coreName + " is not a valid material. Falling back to HEAVY_CORE.");
            core = Material.HEAVY_CORE;
        }
        coreItem = core;

        Map<Material, Integer> parsed = new LinkedHashMap<>();
        ConfigurationSection section = config.getConfigurationSection("multipliers");
        if (section != null) {
            for (String raw : section.getKeys(false)) {
                Material material = Material.matchMaterial(raw);
                if (material == null) {
                    getLogger().warning("Unknown material in multipliers: " + raw);
                    continue;
                }
                int value = section.getInt(raw, 1);
                if (value < 1) {
                    getLogger().warning("Multiplier for " + raw + " is below 1, ignoring.");
                    continue;
                }
                parsed.put(material, value);
            }
        }
        if (parsed.isEmpty()) {
            getLogger().warning("No usable multipliers configured; the multiplier slot will reject every item.");
        }
        multipliers = parsed;
    }

    /** The tick loop only wakes every LOOP_PERIOD_TICKS, so intervals snap to that grid. */
    private static int roundToPeriod(int ticks) {
        int value = Math.max(LOOP_PERIOD_TICKS, ticks);
        int remainder = value % LOOP_PERIOD_TICKS;
        return remainder == 0 ? value : value + (LOOP_PERIOD_TICKS - remainder);
    }

    private void debug(String message) {
        if (debug) {
            getLogger().info("[debug] " + message);
        }
    }

    // ------------------------------------------------------------------- storage

    private void markDirty() {
        dirty = true;
    }

    private void loadStorage() {
        spawners.clear();
        aliveCounts.clear();
        if (storageFile == null || !storageFile.exists()) {
            return;
        }

        YamlConfiguration yaml = new YamlConfiguration();
        // Location keys use ';' as their separator and YAML paths use '/', so neither
        // a world name containing a dot nor a coordinate can split a path by accident.
        yaml.options().pathSeparator('/');
        try {
            yaml.load(storageFile);
        } catch (Exception ex) {
            getLogger().severe("Failed to read spawners.yml: " + ex.getMessage());
            getLogger().severe("Starting with no tracked spawners. Fix or remove the file before restarting.");
            return;
        }

        for (String key : yaml.getKeys(false)) {
            ConfigurationSection section = yaml.getConfigurationSection(key);
            if (section == null) {
                continue;
            }
            SpawnerData data = new SpawnerData();
            data.egg = section.getItemStack("egg");
            data.multiplierItem = section.getItemStack("multiplier");
            data.core = section.getItemStack("core");

            String typeName = section.getString("original-type");
            if (typeName != null) {
                try {
                    data.originalType = EntityType.valueOf(typeName.toUpperCase(Locale.ROOT));
                } catch (IllegalArgumentException ex) {
                    getLogger().warning("Unknown original-type " + typeName + " for " + key);
                }
            }
            // Defaults to "captured if we stored a type", so files written by earlier
            // versions still load with the right meaning.
            data.originalCaptured = section.getBoolean("original-captured", data.originalType != null);
            data.ticksLeft = intervalFor(data);
            spawners.put(key, data);
            aliveCounts.put(key, 0);   // corrected by the first reconcile
        }
        getLogger().info("Loaded " + spawners.size() + " spawner(s) from storage.");
    }

    private void saveStorage() {
        if (storageFile == null) {
            return;
        }
        YamlConfiguration yaml = new YamlConfiguration();
        yaml.options().pathSeparator('/');

        for (Map.Entry<String, SpawnerData> entry : spawners.entrySet()) {
            String base = entry.getKey();
            SpawnerData data = entry.getValue();
            // REQ-9: an adopted spawner with nothing in it and no captured type would
            // otherwise serialise as an empty section and be lost on the next load,
            // coming back suppressed but untracked - permanently silent.
            yaml.set(base + "/tracked", true);
            yaml.set(base + "/egg", data.egg);
            yaml.set(base + "/multiplier", data.multiplierItem);
            yaml.set(base + "/core", data.core);
            yaml.set(base + "/original-type", data.originalType == null ? null : data.originalType.name());
            yaml.set(base + "/original-captured", data.originalCaptured);
        }

        try {
            if (!getDataFolder().exists() && !getDataFolder().mkdirs()) {
                getLogger().severe("Could not create the plugin data folder; spawner storage not saved.");
                return;
            }
            yaml.save(storageFile);
            dirty = false;
        } catch (Exception ex) {
            getLogger().severe("Failed to write spawners.yml: " + ex.getMessage());
        }
    }

    // ----------------------------------------------------------------- key utils

    private static String locationKey(Location location) {
        World world = location.getWorld();
        return (world == null ? "?" : world.getName()) + ";"
                + location.getBlockX() + ";" + location.getBlockY() + ";" + location.getBlockZ();
    }

    /** Parses from the right, so a world name containing ';' still round-trips. */
    private Location keyToLocation(String key) {
        int z = key.lastIndexOf(';');
        if (z <= 0) {
            return null;
        }
        int y = key.lastIndexOf(';', z - 1);
        if (y <= 0) {
            return null;
        }
        int x = key.lastIndexOf(';', y - 1);
        if (x <= 0) {
            return null;
        }
        World world = getServer().getWorld(key.substring(0, x));
        if (world == null) {
            return null;
        }
        try {
            return new Location(world,
                    Integer.parseInt(key.substring(x + 1, y)),
                    Integer.parseInt(key.substring(y + 1, z)),
                    Integer.parseInt(key.substring(z + 1)));
        } catch (NumberFormatException ex) {
            return null;
        }
    }

    private static ItemStack copyOrNull(ItemStack item) {
        return item == null || item.getType().isAir() || item.getAmount() <= 0 ? null : item.clone();
    }

    private static String prettyName(EntityType type) {
        if (type == null) {
            return "none";
        }
        StringBuilder out = new StringBuilder();
        for (String part : type.name().toLowerCase(Locale.ROOT).split("_")) {
            if (part.isEmpty()) {
                continue;
            }
            if (out.length() > 0) {
                out.append(' ');
            }
            out.append(Character.toUpperCase(part.charAt(0))).append(part.substring(1));
        }
        return out.toString();
    }

    /** ZOMBIE_SPAWN_EGG becomes EntityType.ZOMBIE; anything that is not an egg is null. */
    private static EntityType eggType(ItemStack item) {
        if (item == null || item.getType().isAir()) {
            return null;
        }
        String name = item.getType().name();
        if (!name.endsWith(SUFFIX_SPAWN_EGG)) {
            return null;
        }
        try {
            return EntityType.valueOf(name.substring(0, name.length() - SUFFIX_SPAWN_EGG.length()));
        } catch (IllegalArgumentException ex) {
            return null;
        }
    }

    private boolean hasCore(SpawnerData data) {
        return data.core != null && data.core.getType() == coreItem && data.core.getAmount() > 0;
    }

    private int intervalFor(SpawnerData data) {
        return hasCore(data) ? boostedInterval : spawnInterval;
    }

    private int multiplierFor(ItemStack item) {
        if (item == null || item.getType().isAir()) {
            return 1;
        }
        return Math.max(1, multipliers.getOrDefault(item.getType(), 1));
    }

    /** REQ-4 / section 6: what this spawner should actually produce right now. */
    private EntityType activeType(SpawnerData data) {
        EntityType fromEgg = eggType(data.egg);
        return fromEgg != null ? fromEgg : data.originalType;
    }

    // ------------------------------------------------------------------ tick loop

    private void tick() {
        cycleCounter++;

        if (cycleCounter % RECONCILE_EVERY_CYCLES == 0) {
            reconcileCounts();
            // Re-assert managed state so external resets (/setblock, WorldEdit, other
            // plugins) are corrected instead of leaving a half-vanilla spawner (REQ-3).
            for (SpawnerData data : spawners.values()) {
                data.applied = false;
            }
            reportedFailures.clear();   // a still-broken spawner may warn again
        }

        // REQ-6b: iterate in place rather than copying the map every 10 ticks.
        Iterator<Map.Entry<String, SpawnerData>> iterator = spawners.entrySet().iterator();
        while (iterator.hasNext()) {
            Map.Entry<String, SpawnerData> entry = iterator.next();
            String key = entry.getKey();
            SpawnerData data = entry.getValue();
            try {
                tickSpawner(key, data, iterator);
            } catch (Throwable ex) {
                // One bad spawner must not abort the loop for every other spawner.
                // Without this, a single throw in here is a total outage: no spawner
                // after it in the iteration order ever reaches runSpawnCycle, every
                // tick, and the only symptom is a scheduler warning in console.
                // Throwable rather than Exception: a LinkageError from an API mismatch
                // is exactly the kind of failure that should cost one spawner, not all.
                if (reportedFailures.add(key)) {
                    getLogger().log(Level.WARNING, "Spawner " + key + " threw during its cycle and was"
                            + " skipped; other spawners are unaffected. Reported at most once per"
                            + " 30 second reconcile window.", ex);
                }
            }
        }
    }

    /** One spawner's cycle. Every early return here is a logged exit point (see debug). */
    private void tickSpawner(String key, SpawnerData data, Iterator<Map.Entry<String, SpawnerData>> iterator) {
        // exit 1: world not loaded, or key unparseable.
        // Deliberately does NOT untrack: a world can be absent simply because it has
        // not been loaded yet (Multiverse and friends), and dropping the entry would
        // delete the player items stored in that spawner.
        Location location = keyToLocation(key);
        if (location == null || location.getWorld() == null) {
            debug(key + ": world not loaded or key unparseable, skipping");
            return;
        }

        // exit 2: chunk unloaded
        World world = location.getWorld();
        if (!world.isChunkLoaded(location.getBlockX() >> 4, location.getBlockZ() >> 4)) {
            debug(key + ": chunk not loaded");
            return;
        }

        // exit 3: block is no longer a spawner (WorldEdit, /setblock, another plugin)
        Block block = location.getBlock();
        if (block.getType() != Material.SPAWNER) {
            debug(key + ": block is " + block.getType() + ", untracking");
            syncViewer(key, data);       // capture GUI contents before we drop tracking
            iterator.remove();
            aliveCounts.remove(key);
            markDirty();
            closeViewer(data);
            returnStoredItems(world, location.clone().add(0.5D, 0.5D, 0.5D), data);
            return;
        }

        // Must run before activeType(): originalType is captured here (section 7 item 2).
        if (!data.applied) {
            applyManagedState(block, data);
        }

        // exit 4: nothing to spawn
        EntityType type = activeType(data);
        if (type == null) {
            debug(key + ": no active mob type (no egg and no original type)");
            return;
        }

        // exit 5: nobody around (REQ-5) - checked before the countdown so an
        // unattended spawner pauses instead of banking spawns.
        if (!playerNearby(location)) {
            debug(key + ": no player within " + requiredPlayerRange + " blocks");
            return;
        }

        int interval = intervalFor(data);
        if (data.ticksLeft > interval) {
            data.ticksLeft = interval;   // core inserted mid countdown
        }
        data.ticksLeft -= LOOP_PERIOD_TICKS;

        // exit 6: countdown still running
        if (data.ticksLeft > 0) {
            return;
        }
        data.ticksLeft = interval;
        runSpawnCycle(key, data, block, type);
    }

    /**
     * REQ-5: iterate the world player list, which is a short in-memory list, rather
     * than scanning entities around every spawner.
     */
    private boolean playerNearby(Location location) {
        if (requiredPlayerRange <= 0) {
            return true;
        }
        World world = location.getWorld();
        if (world == null) {
            return false;
        }
        double rangeSquared = (double) requiredPlayerRange * requiredPlayerRange;
        for (Player player : world.getPlayers()) {
            if (player.getGameMode() == GameMode.SPECTATOR) {
                continue;
            }
            if (player.getLocation().distanceSquared(location) <= rangeSquared) {
                return true;
            }
        }
        return false;
    }

    // -------------------------------------------------------- managed block state

    /** Parks vanilla behaviour on the block and records the original mob (REQ-3, REQ-4). */
    private void applyManagedState(Block block, SpawnerData data) {
        BlockState state = block.getState();
        if (!(state instanceof CreatureSpawner spawner)) {
            return;
        }

        // REQ-4: capture once, before anything is overwritten. getSpawnedType() is
        // @Nullable and returns null for a blank spawner, so record the read itself.
        if (!data.originalCaptured) {
            try {
                data.originalType = spawner.getSpawnedType();
                data.originalCaptured = true;
                markDirty();
            } catch (Exception ex) {
                // Could not read it; leave uncaptured and retry on the next re-assert
                // rather than recording a blank we are not sure about.
                debug("could not read the original spawned type: " + ex.getMessage());
            }
        }

        EntityType display = activeType(data);
        try {
            if (display != null) {
                spawner.setSpawnedType(display);
            } else if (data.originalCaptured) {
                // The block was blank and the egg has been removed. setSpawnedType(null)
                // blanks it again instead of leaving the egg's type baked in.
                spawner.setSpawnedType(null);
            }
        } catch (Exception ex) {
            debug("could not set spawned type " + display + ": " + ex.getMessage());
        }

        spawner.setSpawnCount(0);                    // a fired timer produces nothing

        // ORDER MATTERS. setMinSpawnDelay validates min <= max, so raising min to 32767
        // while max is still the vanilla 800 throws IllegalArgumentException - and the
        // throw happens before update(), so nothing is applied and every later spawner
        // in the tick loop is skipped too. Widening the window: raise max first.
        spawner.setMaxSpawnDelay(SUPPRESSED_DELAY);
        spawner.setMinSpawnDelay(SUPPRESSED_DELAY);
        spawner.setDelay(SUPPRESSED_DELAY);          // REQ-3: must stay in short range
        spawner.setRequiredPlayerRange(0);
        spawner.update(true, false);

        data.applied = true;
    }

    /** Undoes every field applyManagedState touched, including the mob type (REQ-4, REQ-10). */
    private void restoreVanillaState(Block block, SpawnerData data) {
        if (block.getType() != Material.SPAWNER) {
            return;
        }
        BlockState state = block.getState();
        if (!(state instanceof CreatureSpawner spawner)) {
            return;
        }

        // A captured null is a blank spawner and must be restored as blank (REQ-4).
        if (data != null && data.originalCaptured) {
            try {
                spawner.setSpawnedType(data.originalType);
            } catch (Exception ex) {
                debug("could not restore spawned type: " + ex.getMessage());
            }
        }

        spawner.setSpawnCount(VANILLA_SPAWN_COUNT);

        // ORDER MATTERS, mirrored from applyManagedState. This narrows the window
        // (32767/32767 down to 200/800), so lower min first: 200 <= 32767 passes, and
        // 800 >= 200 passes afterwards. Setting max to 800 first would throw.
        spawner.setMinSpawnDelay(VANILLA_MIN_SPAWN_DELAY);
        spawner.setMaxSpawnDelay(VANILLA_MAX_SPAWN_DELAY);
        spawner.setDelay(VANILLA_DELAY);
        spawner.setRequiredPlayerRange(VANILLA_PLAYER_RANGE);
        spawner.update(true, false);
    }

    /**
     * REQ-10: hand every managed spawner back to vanilla on shutdown so an uninstall
     * does not leave permanently dead blocks. Best effort: spawners in unloaded chunks
     * cannot be touched, and a hard crash skips onDisable entirely.
     */
    private void releaseAllToVanilla() {
        int released = 0;
        for (Map.Entry<String, SpawnerData> entry : spawners.entrySet()) {
            Location location = keyToLocation(entry.getKey());
            if (location == null || location.getWorld() == null) {
                continue;
            }
            World world = location.getWorld();
            if (!world.isChunkLoaded(location.getBlockX() >> 4, location.getBlockZ() >> 4)) {
                continue;
            }
            Block block = location.getBlock();
            if (block.getType() != Material.SPAWNER) {
                continue;
            }
            restoreVanillaState(block, entry.getValue());
            released++;
        }
        getLogger().info("Released " + released + " spawner(s) to vanilla behaviour"
                + (released < spawners.size() ? " (" + (spawners.size() - released) + " in unloaded chunks skipped)" : "")
                + ".");
    }

    // ----------------------------------------------------------------- spawn cycle

    private void runSpawnCycle(String key, SpawnerData data, Block block, EntityType type) {
        // exit 7: the type has no spawnable entity class at all.
        // Deliberately not gated on EntityType#isSpawnable() - see spec section 7 item 1;
        // an over-eager guard there is exactly what silently kills ordinary mobs.
        if (type.getEntityClass() == null) {
            debug(key + ": entity type " + type + " has no entity class");
            return;
        }

        // exit 8: no room directly above the spawner
        Block above = block.getRelative(BlockFace.UP);
        if (!above.isPassable()) {
            debug(key + ": block above is " + above.getType() + " (not passable)");
            return;
        }

        int alive = aliveCounts.getOrDefault(key, 0);
        if (alive >= mobCap) {
            debug(key + ": at mob cap (" + alive + "/" + mobCap + ")");
            return;
        }

        int batch = data.egg != null ? data.egg.getAmount() : VANILLA_SPAWN_COUNT;
        batch = Math.min(Math.max(1, batch), maxMobsPerCycle);
        batch = Math.min(batch, mobCap - alive);
        if (batch <= 0) {
            debug(key + ": batch size resolved to 0");
            return;
        }

        int multiplier = multiplierFor(data.multiplierItem);
        World world = block.getWorld();
        Location base = block.getLocation().add(0.5D, 1.0D, 0.5D);

        int spawned = 0;
        for (int i = 0; i < batch; i++) {
            Location target = base.clone();
            target.setYaw(ThreadLocalRandom.current().nextFloat() * 360.0F);   // random yaw only
            target.setPitch(0.0F);

            Entity entity;
            try {
                // REQ-7: the consumer runs before CreatureSpawnEvent, so other plugins
                // can see the ownership tag when they decide whether to allow the spawn.
                entity = world.spawnEntity(target, type, CreatureSpawnEvent.SpawnReason.SPAWNER,
                        spawnedEntity -> prepareMob(spawnedEntity, key, multiplier));
            } catch (IllegalArgumentException | IllegalStateException ex) {
                debug(key + ": spawn of " + type + " threw " + ex.getClass().getSimpleName() + ": " + ex.getMessage());
                return;
            }

            // REQ-7: a denied spawn must not count, or a protected region jams the
            // spawner permanently at the cap.
            if (entity == null || !entity.isValid()) {
                debug(key + ": spawn of " + type + " was denied or removed immediately");
                continue;
            }
            spawned++;
        }

        if (spawned > 0) {
            aliveCounts.merge(key, spawned, Integer::sum);
            debug(key + ": spawned " + spawned + "x " + type + " (alive " + aliveCounts.get(key) + "/" + mobCap + ")");
        }
    }

    /** Runs inside the spawn consumer, before CreatureSpawnEvent fires. */
    private void prepareMob(Entity entity, String key, int multiplier) {
        PersistentDataContainer container = entity.getPersistentDataContainer();
        container.set(keyOwner, PersistentDataType.STRING, key);
        if (multiplier > 1) {
            container.set(keyMultiplier, PersistentDataType.INTEGER, multiplier);
        }

        if (!(entity instanceof LivingEntity living)) {
            return;
        }

        // REQ-1 layer 1: player items must never be able to reach the drop list.
        living.setCanPickupItems(false);
        EntityEquipment equipment = living.getEquipment();
        if (equipment == null) {
            return;
        }
        try {
            equipment.setItemInMainHandDropChance(0.0F);
            equipment.setItemInOffHandDropChance(0.0F);
            equipment.setHelmetDropChance(0.0F);
            equipment.setChestplateDropChance(0.0F);
            equipment.setLeggingsDropChance(0.0F);
            equipment.setBootsDropChance(0.0F);
        } catch (UnsupportedOperationException | IllegalArgumentException ex) {
            debug("could not zero drop chances for " + entity.getType() + ": " + ex.getMessage());
        }
    }

    /**
     * REQ-6a: mobs vanish in ways that fire no death event (despawn, chunk unload,
     * /kill, the void, other plugins). Without this the counter drifts up and every
     * spawner eventually sits at the cap forever.
     *
     * Note this only sees loaded chunks, so a farm whose mobs are unloaded reads as
     * empty and may briefly exceed the cap once those chunks come back.
     *
     * Living entities only: a farm running an 18x multiplier has thousands of dropped
     * items and XP orbs in the air, and a PDC read on each of those every 30 seconds is
     * exactly the lag this plugin exists to avoid. It also matches the incremental path -
     * EntityDeathEvent only fires for living entities, so nothing else could ever be
     * decremented anyway.
     */
    private void reconcileCounts() {
        Map<String, Integer> fresh = new HashMap<>();
        for (World world : getServer().getWorlds()) {
            for (Entity entity : world.getLivingEntities()) {
                String key = entity.getPersistentDataContainer().get(keyOwner, PersistentDataType.STRING);
                if (key == null || !spawners.containsKey(key)) {
                    continue;
                }
                fresh.merge(key, 1, Integer::sum);
            }
        }
        aliveCounts.keySet().retainAll(spawners.keySet());
        for (String key : spawners.keySet()) {
            aliveCounts.put(key, fresh.getOrDefault(key, 0));
        }
        debug("reconciled live counts for " + spawners.size() + " spawner(s)");
    }

    // ---------------------------------------------------------------- mob events

    @EventHandler(priority = EventPriority.HIGH)
    public void onEntityDeath(EntityDeathEvent event) {
        LivingEntity entity = event.getEntity();
        PersistentDataContainer container = entity.getPersistentDataContainer();

        String key = container.get(keyOwner, PersistentDataType.STRING);
        if (key == null) {
            return;
        }
        aliveCounts.computeIfPresent(key, (ignored, alive) -> alive > 0 ? alive - 1 : 0);

        Integer multiplier = container.get(keyMultiplier, PersistentDataType.INTEGER);
        if (multiplier == null || multiplier <= 1) {
            return;
        }

        // REQ-1 layer 2: hold back whatever the mob was carrying, matched one for one.
        List<ItemStack> carried = carriedItems(entity);
        List<ItemStack> drops = event.getDrops();
        List<ItemStack> passthrough = new ArrayList<>();
        List<ItemStack> loot = new ArrayList<>();

        for (ItemStack drop : drops) {
            if (drop == null || drop.getType().isAir()) {
                continue;
            }
            boolean matched = false;
            Iterator<ItemStack> carriedIterator = carried.iterator();
            while (carriedIterator.hasNext()) {
                if (carriedIterator.next().isSimilar(drop)) {
                    carriedIterator.remove();   // consume the match so duplicates line up
                    matched = true;
                    break;
                }
            }
            (matched ? passthrough : loot).add(drop.clone());
        }

        drops.clear();
        drops.addAll(passthrough);
        drops.addAll(multiplyAndMerge(loot, multiplier));

        if (multiplyExperience) {
            long experience = (long) event.getDroppedExp() * multiplier;
            event.setDroppedExp((int) Math.min(experience, Integer.MAX_VALUE));
        }
    }

    private List<ItemStack> carriedItems(LivingEntity entity) {
        List<ItemStack> carried = new ArrayList<>();
        EntityEquipment equipment = entity.getEquipment();
        if (equipment == null) {
            return carried;
        }
        addIfReal(carried, equipment.getItemInMainHand());
        addIfReal(carried, equipment.getItemInOffHand());
        for (ItemStack armour : equipment.getArmorContents()) {
            addIfReal(carried, armour);
        }
        return carried;
    }

    private static void addIfReal(List<ItemStack> target, ItemStack item) {
        ItemStack copy = copyOrNull(item);
        if (copy != null) {
            target.add(copy);
        }
    }

    /** Multiplies loot and merges it into full stacks rather than hundreds of entities. */
    private static List<ItemStack> multiplyAndMerge(List<ItemStack> loot, int multiplier) {
        List<ItemStack> prototypes = new ArrayList<>();
        List<Long> totals = new ArrayList<>();

        for (ItemStack item : loot) {
            long amount = (long) item.getAmount() * multiplier;
            int index = -1;
            for (int i = 0; i < prototypes.size(); i++) {
                if (prototypes.get(i).isSimilar(item)) {
                    index = i;
                    break;
                }
            }
            if (index < 0) {
                ItemStack prototype = item.clone();
                prototype.setAmount(1);
                prototypes.add(prototype);
                totals.add(amount);
            } else {
                totals.set(index, totals.get(index) + amount);
            }
        }

        List<ItemStack> merged = new ArrayList<>();
        for (int i = 0; i < prototypes.size(); i++) {
            ItemStack prototype = prototypes.get(i);
            long remaining = Math.min(totals.get(i), MAX_MERGED_AMOUNT);
            int maxStack = Math.max(1, prototype.getMaxStackSize());
            while (remaining > 0) {
                int take = (int) Math.min(maxStack, remaining);
                ItemStack stack = prototype.clone();
                stack.setAmount(take);
                merged.add(stack);
                remaining -= take;
            }
        }
        return merged;
    }

    /** Backstop for REQ-3: if vanilla ever does fire, nothing comes of it. */
    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onSpawnerSpawn(SpawnerSpawnEvent event) {
        CreatureSpawner spawner = event.getSpawner();
        if (spawner == null) {
            return;
        }
        Block block = spawner.getBlock();
        String key = locationKey(block.getLocation());

        SpawnerData data = spawners.get(key);
        if (data != null) {
            event.setCancelled(true);
            return;
        }

        if (!manageAllSpawners) {
            return;
        }

        // Section 6: lazy adoption. A spawner registers itself the first time vanilla
        // would have fired it - no startup scan, no chunk walking.
        data = new SpawnerData();
        EntityType original = null;
        try {
            original = spawner.getSpawnedType();
        } catch (Exception ignored) {
            // fall through to the event entity type
        }
        if (original == null) {
            original = event.getEntityType();
        }
        data.originalType = original;
        // A blank spawner never fires vanilla, so anything adopted through this event
        // has a real type - the read counts as captured.
        data.originalCaptured = original != null;
        data.ticksLeft = intervalFor(data);

        spawners.put(key, data);
        aliveCounts.putIfAbsent(key, 0);
        // REQ-9: adopted spawners must be persisted, or after a restart they come back
        // suppressed but untracked - permanently silent.
        markDirty();

        event.setCancelled(true);
        applyManagedState(block, data);
        debug(key + ": adopted (original type " + data.originalType + ")");
    }

    // -------------------------------------------------------------- block events

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onBlockBreak(BlockBreakEvent event) {
        Block block = event.getBlock();
        if (block.getType() != Material.SPAWNER) {
            return;
        }

        Player player = event.getPlayer();
        String key = locationKey(block.getLocation());
        SpawnerData data = spawners.get(key);
        if (data != null) {
            // Pull the open GUI into SpawnerData first, then untrack, then close: the
            // close handler sees an untracked key and no longer touches the block.
            syncViewer(key, data);
            spawners.remove(key);
            aliveCounts.remove(key);
            markDirty();
            closeViewer(data);
        }

        World world = block.getWorld();
        Location dropLocation = block.getLocation().add(0.5D, 0.5D, 0.5D);

        // REQ-2 part one: stored player items always come back, in every game mode,
        // regardless of isDropItems(). Deleting player deposits is data loss, not a
        // drop rule.
        if (data != null) {
            returnStoredItems(world, dropLocation, data);
        }

        // REQ-2 part two: the block itself respects the normal rules.
        if (!dropSpawnerOnBreak) {
            return;
        }
        boolean creative = player.getGameMode() == GameMode.CREATIVE;
        if (creative && !allowCreativeDrops) {
            return;
        }
        // Protection plugins set isDropItems(false) deliberately; overriding it here
        // would be a griefing bypass. The one exception is a creative break, where the
        // server itself clears the flag to express the vanilla "creative drops nothing"
        // rule - allow-creative-drops is the admin overriding exactly that rule, so
        // honouring the flag there would make the setting do nothing at all.
        if (!event.isDropItems() && !creative) {
            debug(key + ": block drop suppressed by another plugin (isDropItems=false)");
            return;
        }
        if (requireSilkTouch && !hasSilkTouch(player.getInventory().getItemInMainHand())) {
            return;
        }

        // REQ-4: build the item from the original type, never from the inserted egg.
        EntityType dropType = data != null ? data.originalType : spawnedTypeOf(block);
        world.dropItemNaturally(dropLocation, buildSpawnerItem(dropType));
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onEntityExplode(EntityExplodeEvent event) {
        handleExplosion(event.blockList());
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onBlockExplode(BlockExplodeEvent event) {
        handleExplosion(event.blockList());
    }

    /** Explosions destroy the block, but stored player items still come back. */
    private void handleExplosion(List<Block> blocks) {
        for (Block block : blocks) {
            if (block.getType() != Material.SPAWNER) {
                continue;
            }
            String key = locationKey(block.getLocation());
            SpawnerData data = spawners.get(key);
            if (data == null) {
                continue;
            }
            syncViewer(key, data);
            spawners.remove(key);
            aliveCounts.remove(key);
            markDirty();
            closeViewer(data);
            returnStoredItems(block.getWorld(), block.getLocation().add(0.5D, 0.5D, 0.5D), data);
        }
    }

    private void returnStoredItems(World world, Location location, SpawnerData data) {
        for (ItemStack item : new ItemStack[]{data.egg, data.multiplierItem, data.core}) {
            ItemStack copy = copyOrNull(item);
            if (copy != null) {
                world.dropItemNaturally(location, copy);
            }
        }
        data.egg = null;
        data.multiplierItem = null;
        data.core = null;
    }

    private static boolean hasSilkTouch(ItemStack tool) {
        if (tool == null || tool.getType().isAir()) {
            return false;
        }
        try {
            return tool.getEnchantmentLevel(Enchantment.SILK_TOUCH) > 0;
        } catch (Exception ex) {
            return false;
        }
    }

    private EntityType spawnedTypeOf(Block block) {
        BlockState state = block.getState();
        if (!(state instanceof CreatureSpawner spawner)) {
            return null;
        }
        try {
            return spawner.getSpawnedType();
        } catch (Exception ex) {
            return null;
        }
    }

    private ItemStack buildSpawnerItem(EntityType type) {
        ItemStack item = new ItemStack(Material.SPAWNER);
        if (type == null) {
            return item;
        }
        ItemMeta meta = item.getItemMeta();
        if (!(meta instanceof BlockStateMeta blockStateMeta)) {
            return item;
        }
        BlockState state = blockStateMeta.getBlockState();
        if (state instanceof CreatureSpawner spawner) {
            spawner.setSpawnedType(type);
            // Ship vanilla timings inside the item so a replaced block is never born
            // suppressed if the plugin is later removed.
            spawner.setSpawnCount(VANILLA_SPAWN_COUNT);
            spawner.setDelay(VANILLA_DELAY);
            // Same ordering rule: the item's fresh block state is already 200/800, so
            // min goes first and neither call ever crosses the other bound.
            spawner.setMinSpawnDelay(VANILLA_MIN_SPAWN_DELAY);
            spawner.setMaxSpawnDelay(VANILLA_MAX_SPAWN_DELAY);
            spawner.setRequiredPlayerRange(VANILLA_PLAYER_RANGE);
            blockStateMeta.setBlockState(spawner);
            item.setItemMeta(blockStateMeta);
        }
        return item;
    }

    // ---------------------------------------------------------------- GUI events

    @EventHandler(priority = EventPriority.HIGH)
    public void onInteract(PlayerInteractEvent event) {
        if (event.getAction() != Action.RIGHT_CLICK_BLOCK || event.getHand() != EquipmentSlot.HAND) {
            return;
        }
        // Not ignoreCancelled: PlayerInteractEvent arrives pre-cancelled in ordinary
        // situations (adventure mode, some held items). Only a real DENY on the block
        // interaction - a protection plugin - should stop the GUI.
        if (event.useInteractedBlock() == Event.Result.DENY) {
            return;
        }
        Block block = event.getClickedBlock();
        if (block == null || block.getType() != Material.SPAWNER) {
            return;
        }

        Player player = event.getPlayer();
        ItemStack held = player.getInventory().getItemInMainHand();

        // Sneak with a block in hand to place against a spawner as usual. Spawn eggs
        // are not blocks, so the vanilla "egg rewrites the spawner" path stays closed.
        if (player.isSneaking() && !held.getType().isAir() && held.getType().isBlock()) {
            return;
        }

        event.setCancelled(true);
        if (!player.hasPermission("spawnerplus.use")) {
            player.sendMessage(Component.text("You cannot open spawners here.", NamedTextColor.RED));
            return;
        }
        openGui(player, block);
    }

    private void openGui(Player player, Block block) {
        String key = locationKey(block.getLocation());
        SpawnerData data = spawners.get(key);
        if (data == null) {
            data = new SpawnerData();
            data.ticksLeft = intervalFor(data);
            spawners.put(key, data);
            aliveCounts.putIfAbsent(key, 0);
            markDirty();
        }

        // applyManagedState captures originalType (REQ-4) before the egg overwrites it.
        if (!data.applied) {
            applyManagedState(block, data);
        }

        if (data.viewer != null && !data.viewer.equals(player.getUniqueId()) && isViewing(data.viewer, key)) {
            player.sendMessage(Component.text("Someone else is using this spawner.", NamedTextColor.RED));
            return;
        }

        SpawnerHolder holder = new SpawnerHolder(key);
        Inventory inventory = getServer().createInventory(holder, GUI_SIZE,
                Component.text("Spawner", NamedTextColor.DARK_GRAY));
        holder.inventory = inventory;

        ItemStack filler = pane(Material.BLACK_STAINED_GLASS_PANE, Component.empty(), List.of());
        for (int slot = 0; slot < GUI_SIZE; slot++) {
            inventory.setItem(slot, filler);
        }

        inventory.setItem(SLOT_LABEL_EGG, pane(Material.LIME_STAINED_GLASS_PANE,
                Component.text("Spawn Egg Slot", NamedTextColor.GREEN),
                List.of("Sets which mob this spawner produces.",
                        "Stack size sets how many spawn per cycle.",
                        "Capped at " + maxMobsPerCycle + " per cycle.")));

        // REQ-8: Minecraft does not wrap lore, so every entry is its own line.
        List<String> multiplierLore = new ArrayList<>();
        multiplierLore.add("Sets the drop and XP multiplier.");
        multiplierLore.add("Stack size does not matter.");
        multiplierLore.add("");
        List<Map.Entry<Material, Integer>> sortedMultipliers =
                new ArrayList<Map.Entry<Material, Integer>>(multipliers.entrySet());
        sortedMultipliers.sort((left, right) -> Integer.compare(left.getValue(), right.getValue()));
        for (Map.Entry<Material, Integer> entry : sortedMultipliers) {
            multiplierLore.add(prettyMaterial(entry.getKey()) + " x" + entry.getValue());
        }
        inventory.setItem(SLOT_LABEL_MULTIPLIER, pane(Material.YELLOW_STAINED_GLASS_PANE,
                Component.text("Multiplier Slot", NamedTextColor.YELLOW), multiplierLore));

        inventory.setItem(SLOT_LABEL_CORE, pane(Material.MAGENTA_STAINED_GLASS_PANE,
                Component.text("Speed Core Slot", NamedTextColor.LIGHT_PURPLE),
                List.of("Insert " + prettyMaterial(coreItem) + " to halve the interval.",
                        "Normal: " + spawnInterval + " ticks",
                        "Boosted: " + boostedInterval + " ticks")));

        inventory.setItem(SLOT_EGG, copyOrNull(data.egg));
        inventory.setItem(SLOT_MULTIPLIER, copyOrNull(data.multiplierItem));
        inventory.setItem(SLOT_CORE, copyOrNull(data.core));
        refreshStatus(inventory, key, data);

        data.viewer = player.getUniqueId();
        player.openInventory(inventory);
    }

    private boolean isViewing(UUID uuid, String key) {
        Player player = getServer().getPlayer(uuid);
        if (player == null) {
            return false;
        }
        InventoryHolder holder = player.getOpenInventory().getTopInventory().getHolder();
        return holder instanceof SpawnerHolder spawnerHolder && spawnerHolder.key.equals(key);
    }

    /**
     * Copies an open GUI back into SpawnerData. Clicks are only reflected in the
     * inventory a tick later, so anything that untracks a spawner must call this
     * before it removes the entry or a just-deposited item is lost.
     */
    private void syncViewer(String key, SpawnerData data) {
        if (data.viewer == null) {
            return;
        }
        Player player = getServer().getPlayer(data.viewer);
        if (player == null) {
            return;
        }
        Inventory top = player.getOpenInventory().getTopInventory();
        if (top.getHolder() instanceof SpawnerHolder holder && holder.key.equals(key)) {
            syncFromInventory(key, top, player);
        }
    }

    private void closeViewer(SpawnerData data) {
        if (data.viewer == null) {
            return;
        }
        Player player = getServer().getPlayer(data.viewer);
        if (player != null && player.getOpenInventory().getTopInventory().getHolder() instanceof SpawnerHolder) {
            player.closeInventory();
        }
        data.viewer = null;
    }

    private void refreshStatus(Inventory inventory, String key, SpawnerData data) {
        EntityType type = activeType(data);
        int multiplier = multiplierFor(data.multiplierItem);
        int interval = intervalFor(data);
        int alive = aliveCounts.getOrDefault(key, 0);

        List<String> lore = new ArrayList<>();
        lore.add("Mob: " + prettyName(type) + (eggType(data.egg) == null && type != null ? " (native)" : ""));
        lore.add("Interval: " + interval + " ticks (" + String.format(Locale.ROOT, "%.1f", interval / 20.0D) + "s)"
                + (hasCore(data) ? " boosted" : ""));
        lore.add("Live mobs: " + alive + " / " + mobCap);
        lore.add("Per cycle: " + Math.min(data.egg != null ? data.egg.getAmount() : VANILLA_SPAWN_COUNT, maxMobsPerCycle));
        lore.add("Multiplier: x" + multiplier);
        lore.add(requiredPlayerRange > 0
                ? "Needs a player within " + requiredPlayerRange + " blocks"
                : "No player range requirement");
        lore.add("Spawns one block above, fixed point");

        inventory.setItem(SLOT_STATUS, pane(Material.COMPARATOR,
                Component.text("Spawner Status", NamedTextColor.AQUA), lore));
    }

    private static ItemStack pane(Material material, Component name, List<String> lore) {
        ItemStack item = new ItemStack(material);
        ItemMeta meta = item.getItemMeta();
        if (meta != null) {
            meta.displayName(name.decoration(TextDecoration.ITALIC, false));
            List<Component> lines = new ArrayList<>();
            for (String line : lore) {
                lines.add(Component.text(line, NamedTextColor.GRAY).decoration(TextDecoration.ITALIC, false));
            }
            meta.lore(lines);
            item.setItemMeta(meta);
        }
        return item;
    }

    private static String prettyMaterial(Material material) {
        StringBuilder out = new StringBuilder();
        for (String part : material.name().toLowerCase(Locale.ROOT).split("_")) {
            if (part.isEmpty()) {
                continue;
            }
            if (out.length() > 0) {
                out.append(' ');
            }
            out.append(Character.toUpperCase(part.charAt(0))).append(part.substring(1));
        }
        return out.toString();
    }

    private boolean isEditableSlot(int slot) {
        return slot == SLOT_EGG || slot == SLOT_MULTIPLIER || slot == SLOT_CORE;
    }

    private boolean isValidFor(int slot, ItemStack item) {
        if (item == null || item.getType().isAir()) {
            return true;   // taking an item out is always fine
        }
        return switch (slot) {
            case SLOT_EGG -> eggType(item) != null;
            case SLOT_MULTIPLIER -> multipliers.containsKey(item.getType());
            case SLOT_CORE -> item.getType() == coreItem;
            default -> false;
        };
    }

    private int targetSlotFor(ItemStack item) {
        if (eggType(item) != null) {
            return SLOT_EGG;
        }
        if (multipliers.containsKey(item.getType())) {
            return SLOT_MULTIPLIER;
        }
        if (item.getType() == coreItem) {
            return SLOT_CORE;
        }
        return -1;
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onInventoryClick(InventoryClickEvent event) {
        if (!(event.getInventory().getHolder() instanceof SpawnerHolder holder)) {
            return;
        }
        SpawnerData data = spawners.get(holder.key);
        if (data == null) {
            event.setCancelled(true);
            event.getWhoClicked().closeInventory();
            return;
        }
        if (!(event.getWhoClicked() instanceof Player player)) {
            event.setCancelled(true);
            return;
        }

        int raw = event.getRawSlot();
        if (raw < 0) {
            return;   // clicked outside the window
        }

        ClickType click = event.getClick();
        if (click == ClickType.DOUBLE_CLICK) {
            // Collect-to-cursor pulls from every matching slot at once, which would
            // strip the managed slots behind our back.
            event.setCancelled(true);
            return;
        }

        if (raw < GUI_SIZE) {
            if (!isEditableSlot(raw)) {
                event.setCancelled(true);
                return;
            }
            ItemStack incoming = event.getCursor();
            if (click == ClickType.NUMBER_KEY) {
                incoming = player.getInventory().getItem(event.getHotbarButton());
            } else if (click == ClickType.SWAP_OFFHAND) {
                incoming = player.getInventory().getItemInOffHand();
            }
            if (!isValidFor(raw, incoming)) {
                event.setCancelled(true);
                player.sendMessage(Component.text("That item does not belong in this slot.", NamedTextColor.RED));
                return;
            }
            scheduleSync(holder.key, event.getInventory(), player);
            return;
        }

        // Player inventory half: only shift-click needs routing.
        if (event.isShiftClick()) {
            event.setCancelled(true);
            ItemStack moving = event.getCurrentItem();
            if (moving == null || moving.getType().isAir()) {
                return;
            }
            int target = targetSlotFor(moving);
            if (target < 0) {
                return;
            }

            Inventory gui = event.getInventory();
            ItemStack existing = gui.getItem(target);
            if (existing == null || existing.getType().isAir()) {
                gui.setItem(target, moving.clone());
                event.setCurrentItem(null);
            } else if (existing.isSimilar(moving)) {
                int space = existing.getMaxStackSize() - existing.getAmount();
                if (space <= 0) {
                    return;
                }
                int moved = Math.min(space, moving.getAmount());
                existing.setAmount(existing.getAmount() + moved);
                gui.setItem(target, existing);
                moving.setAmount(moving.getAmount() - moved);
                event.setCurrentItem(moving.getAmount() > 0 ? moving : null);
            } else {
                return;
            }
            scheduleSync(holder.key, gui, player);
        }
    }

    @EventHandler(priority = EventPriority.HIGH, ignoreCancelled = true)
    public void onInventoryDrag(InventoryDragEvent event) {
        if (!(event.getInventory().getHolder() instanceof SpawnerHolder holder)) {
            return;
        }
        SpawnerData data = spawners.get(holder.key);
        if (data == null) {
            event.setCancelled(true);
            return;
        }

        boolean touchesGui = false;
        for (int raw : event.getRawSlots()) {
            if (raw >= GUI_SIZE) {
                continue;
            }
            touchesGui = true;
            if (!isEditableSlot(raw) || !isValidFor(raw, event.getOldCursor())) {
                event.setCancelled(true);
                return;
            }
        }
        if (touchesGui && event.getWhoClicked() instanceof Player player) {
            scheduleSync(holder.key, event.getInventory(), player);
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onInventoryClose(InventoryCloseEvent event) {
        if (!(event.getInventory().getHolder() instanceof SpawnerHolder holder)) {
            return;
        }
        SpawnerData data = spawners.get(holder.key);
        if (data == null) {
            return;
        }
        if (event.getPlayer() instanceof Player player) {
            syncFromInventory(holder.key, event.getInventory(), player);
        }
        if (data.viewer != null && data.viewer.equals(event.getPlayer().getUniqueId())) {
            data.viewer = null;
        }

        boolean empty = data.egg == null && data.multiplierItem == null && data.core == null;
        if (!empty) {
            return;
        }

        if (manageAllSpawners) {
            // Section 6: emptying must not untrack. The spawner reverts to its native
            // mob and keeps running under plugin control.
            data.applied = false;
            markDirty();
            return;
        }

        // manage-all-spawners: false - hand the block back to vanilla.
        releaseSpawner(holder.key, data);
    }

    private void releaseSpawner(String key, SpawnerData data) {
        Location location = keyToLocation(key);
        if (location != null && location.getWorld() != null
                && location.getWorld().isChunkLoaded(location.getBlockX() >> 4, location.getBlockZ() >> 4)) {
            restoreVanillaState(location.getBlock(), data);
        }
        spawners.remove(key);
        aliveCounts.remove(key);
        markDirty();
        debug(key + ": released to vanilla");
    }

    /**
     * Bukkit applies the click after the event returns, so the slot contents are only
     * final one tick later.
     */
    private void scheduleSync(String key, Inventory inventory, Player player) {
        getServer().getScheduler().runTask(this, () -> syncFromInventory(key, inventory, player));
    }

    private void syncFromInventory(String key, Inventory inventory, Player player) {
        SpawnerData data = spawners.get(key);
        if (data == null) {
            return;
        }

        ItemStack egg = sanitiseSlot(inventory, SLOT_EGG, player);
        ItemStack multiplierItem = sanitiseSlot(inventory, SLOT_MULTIPLIER, player);
        ItemStack core = sanitiseSlot(inventory, SLOT_CORE, player);

        EntityType before = activeType(data);
        data.egg = copyOrNull(egg);
        data.multiplierItem = copyOrNull(multiplierItem);
        data.core = copyOrNull(core);

        if (!Objects.equals(before, activeType(data))) {
            data.applied = false;   // the block visual and spawned type need updating
        }
        markDirty();
        refreshStatus(inventory, key, data);
    }

    /** Defensive: anything invalid that slipped into a slot goes back to the player. */
    private ItemStack sanitiseSlot(Inventory inventory, int slot, Player player) {
        ItemStack item = inventory.getItem(slot);
        if (item == null || item.getType().isAir()) {
            return null;
        }
        if (isValidFor(slot, item)) {
            return item;
        }
        inventory.setItem(slot, null);
        if (player != null) {
            for (ItemStack leftover : player.getInventory().addItem(item).values()) {
                player.getWorld().dropItemNaturally(player.getLocation(), leftover);
            }
        }
        return null;
    }

    // -------------------------------------------------------------------- command

    @Override
    public boolean onCommand(CommandSender sender, Command command, String label, String[] args) {
        if (args.length == 0) {
            sender.sendMessage(Component.text("/" + label + " <reload|info|debug|release>", NamedTextColor.YELLOW));
            return true;
        }

        switch (args[0].toLowerCase(Locale.ROOT)) {
            case "reload" -> {
                reloadConfig();
                loadSettings();
                for (SpawnerData data : spawners.values()) {
                    data.applied = false;
                    data.ticksLeft = Math.min(data.ticksLeft, intervalFor(data));
                }
                sender.sendMessage(Component.text("SpawnerPlus config reloaded.", NamedTextColor.GREEN));
            }
            case "info" -> {
                int live = 0;
                for (int count : aliveCounts.values()) {
                    live += count;
                }
                sender.sendMessage(Component.text("Tracked spawners: " + spawners.size(), NamedTextColor.AQUA));
                sender.sendMessage(Component.text("Live owned mobs: " + live, NamedTextColor.AQUA));
                sender.sendMessage(Component.text("Interval: " + spawnInterval + " / boosted " + boostedInterval
                        + " ticks, cap " + mobCap, NamedTextColor.AQUA));
                sender.sendMessage(Component.text("manage-all-spawners: " + manageAllSpawners
                        + ", debug: " + debug, NamedTextColor.AQUA));
            }
            case "debug" -> {
                debug = !debug;
                getConfig().set("debug", debug);
                saveConfig();
                sender.sendMessage(Component.text("Debug logging " + (debug ? "enabled" : "disabled") + ".",
                        NamedTextColor.GREEN));
            }
            case "release" -> {
                if (!(sender instanceof Player player)) {
                    sender.sendMessage(Component.text("Players only.", NamedTextColor.RED));
                    return true;
                }
                Block target = player.getTargetBlockExact(6);
                if (target == null || target.getType() != Material.SPAWNER) {
                    player.sendMessage(Component.text("Look at a spawner within 6 blocks.", NamedTextColor.RED));
                    return true;
                }
                String key = locationKey(target.getLocation());
                SpawnerData data = spawners.get(key);
                if (data == null) {
                    player.sendMessage(Component.text("That spawner is not tracked.", NamedTextColor.RED));
                    return true;
                }
                syncViewer(key, data);
                releaseSpawner(key, data);
                closeViewer(data);
                returnStoredItems(target.getWorld(), target.getLocation().add(0.5D, 0.5D, 0.5D), data);
                player.sendMessage(Component.text("Spawner released to vanilla.", NamedTextColor.GREEN));
            }
            default -> sender.sendMessage(Component.text("Unknown subcommand.", NamedTextColor.RED));
        }
        return true;
    }
}
