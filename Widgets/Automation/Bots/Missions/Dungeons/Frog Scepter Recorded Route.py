import os
from typing import Any, Callable, Dict, Generator, List, Optional, Tuple
import random, time, math
import inspect
import PyInventory
import PyAgent
from Py4GWCoreLib import *
import Py4GW
from Py4GWCoreLib import (
    Agent,
    Botting,
    ConsoleLog,
    Effects,
    GLOBAL_CACHE,
    Map,
    Player,
    Range,
    Routines,
    SharedCommandType,
    CombatPrepSkillsType,
    AgentArray,
    AutoPathing,
    IniHandler,
)
from Py4GW_widget_manager import get_widget_handler
from Py4GWCoreLib.py4gwcorelib_src.BehaviorTree import BehaviorTree
from Py4GWCoreLib.routines_src.BehaviourTrees import BT
from Py4GWCoreLib.routines_src.Yield import Utils
from Py4GWCoreLib.routines_src.Yield import Yield
from Widgets.System.Messaging import get_inventory_count, reset_inventory_count

# ==================== CONFIGURATION ====================
BOT_NAME = "Bogroot Growths Recorded Route"
MODULE_ICON = "Textures\\Module_Icons\\Bogroot Growths.png"
MODULE_TAGS = ["Frog Scepter", "BOG", "Frog", "Asura", "Drawf", "Rep", "Recorded Route"]

# Widgets you want to force-manage at startup.
# Edit these lists to choose which widgets to enable/disable.
WIDGETS_TO_ENABLE: tuple[str, ...] = (
    "HeroAI",
    "LootManager",
    "Return to outpost on defeat",
)
WIDGETS_TO_DISABLE: tuple[str, ...] = (
    "InventoryPlus",
    "Inventory Plus",
)
_ALT_ONLY_DISABLE_WIDGETS: tuple[str, ...] = (
    BOT_NAME,
    "Bogroot Growths",
    "Frog Farm Modular",
    "Frog Scepter bot",
    "Frog Scepter",
)

# ==================== CONFIG ====================
_SETTINGS_SECTION     = "Settings"
_STATS_SECTION        = "Statistics"
_FROGGY_DROPS_SECTION    = "Froggy Drops"
_FROGGY_SNAPSHOT_SECTION = "Froggy Snapshot"
_FROGGY_RUN_SECTION      = "Froggy Run"
_GB_DROPS_SECTION     = "GB Drops"
_GB_SNAPSHOT_SECTION  = "GB Snapshot"
_GB_RUN_SECTION       = "GB Run"
_MERCHANT_SECTION     = "Froggy Merchant"
_ALT_SALVAGE_SECTION  = "Froggy Alt Salvage Kits"
_CHAR_NAMES_SECTION   = "Character Names"

_settings_ini_path     = os.path.join(Py4GW.Console.get_projects_path(), "Widgets", "Config", f"{BOT_NAME}.ini")
os.makedirs(os.path.dirname(_settings_ini_path), exist_ok=True)
_settings_ini  = IniHandler(_settings_ini_path)
_settings_loaded: bool = False
_save_requested: bool  = False

# ==================== SETTINGS ====================
_use_hard_mode:      bool = True
_randomize_district: bool = True
_use_precons_running: bool = True
_use_precons_level1:  bool = True
_use_precons_level2:  bool = True

_FIXED_ID_KITS_TARGET          = 3
_FIXED_SALVAGE_KITS_TARGET     = 10
_ALT_SALVAGE_TRIGGER_THRESHOLD = 2
_ALT_SALVAGE_POLL_TIMEOUT_MS   = 200
_ALT_SALVAGE_POLL_MAX_TOTAL_MS = 10_000
_FROGGY_IPC_POLL_TIMEOUT_MS       = 200
_FROGGY_IPC_POLL_MAX_TOTAL_MS     = 10_000
_merchant_enabled:                    bool = False
_merchant_id_kits_target:             int  = _FIXED_ID_KITS_TARGET
_merchant_salvage_kits_target:        int  = _FIXED_SALVAGE_KITS_TARGET
_inventory_slots_threshold:           int  = 4
_merchant_store_consumable_materials: bool = False
_merchant_sell_materials:             bool = False
_merchant_sell_rare_mats:             bool = False
_merchant_buy_ectos:                  bool = False
_merchant_ecto_threshold:             int  = 800_000
_DEFAULT_ALT_SETTLE_WAIT_MS    = 2000
_MAX_ALT_SETTLE_WAIT_MS        = 5000
_merchant_alt_wait_ms:                int  = _DEFAULT_ALT_SETTLE_WAIT_MS
_POST_RETURN_TO_ARBOR_SETTLE_MS = 4000
_POST_WIDGET_REENABLE_SETTLE_MS = 2500
_MISSION_MAP_MOVE_TIMEOUT_MS = 60000
_MISSION_MAP_MOVE_RETRY_WAIT_MS = 500
_MISSION_MAP_STUCK_RECOVERY_TIMEOUT_MS = 5000
_MISSION_MAP_STUCK_POST_COMMAND_WAIT_MS = 1000
_MISSION_MAP_STUCK_RECOVERY_OFFSET = 300.0
_PRECOMBAT_PREP_COOLDOWN_MS = 15000
_STUCK_POSITION_SECONDS = 20.0
_STUCK_POSITION_RADIUS = 250.0
_STUCK_COMMAND_COOLDOWN_SECONDS = 20.0
_last_precombat_prep_ms: int = 0

# ==================== FROGGY STATISTICS ====================
FROGGY_MODEL_IDS    = list(range(1953, 1975))  # all FROGGY variants (domination -> channeling)
FROGGY_MODEL_ID_MIN = FROGGY_MODEL_IDS[0]
FROGGY_MODEL_ID_MAX = FROGGY_MODEL_IDS[-1]

GB_MODEL_ID = 2474  # Glacial Blades

# Persistent stats (loaded from INI, accumulated across all sessions)
_total_runs:     int   = 0
_total_run_time: float = 0.0
_fastest_run:    float = float('inf')
_slowest_run:    float = 0.0
_l1_total_time:  float = 0.0
_l1_fastest:     float = float('inf')
_l1_slowest:     float = 0.0
_l2_total_time:  float = 0.0
_l2_fastest:     float = float('inf')
_l2_slowest:     float = 0.0
_froggy_drops:  dict[str, int] = {}  # account_key -> all-time total (lazily loaded from INI)
_gb_drops:   dict[str, int] = {}  # account_key -> all-time total (lazily loaded from INI)
_char_names: dict[str, str] = {}  # account_key -> character name (populated from live shared memory)

# In-memory session stats (leader only, reset on reload)
_session_runs: int = 0
_session_froggy:  dict[str, int] = {}  # account_key -> drops this session
_session_gb:   dict[str, int] = {}  # account_key -> drops this session

# UI display toggle — not persisted
_scramble_accounts: bool = False

# Run timing anchors (in-memory, reset each run)
_t_run_start: float = 0.0
_t_l2_start:  float = 0.0

# Most-recently-completed times this session (in-memory, updated as each floor/run finishes)
_current_run_time: float = 0.0
_current_l1_time:  float = 0.0
_current_l2_time:  float = 0.0

# Leader pre-chest inventory snapshot
_froggy_pre_snapshot: dict[int, int] = {}  # model_id -> count before chest open
_gb_pre_snapshot:  int            = 0   # GB count before chest open

_FROGGY_ICON_PATH = os.path.join(Py4GW.Console.get_projects_path(), "Widgets", "Automation", "Bots", "Missions", "Dungeons", "Frog Scepter.png")

# ==================== BOT SETUP ====================
TEXTURE = _FROGGY_ICON_PATH

# Map IDs
GADDS_ENCAMPMENT = 638
SPARKFLY = 558
BOGROOT_L1 = 615
BOGROOT_L2 = 616
Great_Temple_of_Balthazar = 248
EyeOfTheNorth = 642

# WhiteList IDs
BOSS_KEY_MODEL_IDS = [25416]  

# Quest IDs
TEKKS_WAR_QUEST_ID = 0x339  # Tekks' War - abandon when in Gadd'Encampment
TEKKS_QUEST_ID = TEKKS_WAR_QUEST_ID

# Dialog IDs
DWARVEN_BLESSING_DIALOG = 0x84
TEKKS_QUEST_TAKE_DIALOG = 0x833901
TEKKS_QUEST_REWARD_DIALOG = 0x833907

# Coordinates
BOGROOT_CHEST_POSITION = (14982.66, -19122.0)
TEKKS_POSITION = (12500, 22648)
BEACON_OF_DROKNAR_ENCODED_NAMES = ((2, 129, 189, 34, 175, 164, 87, 198, 207, 23, 0, 0),)

# ==================== GLOBAL VARIABLES ====================
bot = Botting(
    bot_name=BOT_NAME,
    upkeep_hero_ai_active=False,
    upkeep_auto_loot_active=True,
    upkeep_morale_active=True,
    upkeep_auto_inventory_management_active=True,
)


def _normalize_route_points(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    return [(float(x), float(y)) for x, y in points]


def _mission_map_danger_nearby() -> bool:
    if not Player.IsPlayerLoaded():
        return False
    try:
        px, py = Player.GetXY()
        enemies = Routines.Agents.GetFilteredEnemyArray(px, py, Range.Earshot.value)
        return len(enemies) > 0
    except Exception:
        return False


def _agent_matches_encoded_name(agent_id: int, encoded_names: tuple[tuple[int, ...], ...]) -> bool:
    try:
        agent_encoded = tuple(int(value) for value in PyAgent.PyAgent.GetAgentEncName(agent_id))
    except Exception:
        return False
    return agent_encoded in encoded_names


def _find_encoded_npc_near_xy(
    encoded_names: tuple[tuple[int, ...], ...],
    x: float,
    y: float,
    radius: float = 1200.0,
) -> int:
    npcs = AgentArray.GetNPCMinipetArray()
    npcs = AgentArray.Filter.ByDistance(npcs, (float(x), float(y)), radius)
    npcs = AgentArray.Sort.ByDistance(npcs, (float(x), float(y)))
    for agent_id in npcs:
        aid = int(agent_id)
        if _agent_matches_encoded_name(aid, encoded_names):
            return aid
    return 0


def _interact_encoded_npc_near_xy(
    encoded_names: tuple[tuple[int, ...], ...],
    display_name: str,
    x: float,
    y: float,
    radius: float = 1200.0,
    timeout_ms: int = 10000,
) -> Generator[Any, Any, bool]:
    target_id = _find_encoded_npc_near_xy(encoded_names, x, y, radius)
    if target_id == 0:
        ConsoleLog(
            BOT_NAME,
            f"{display_name}: no encoded NPC found near ({x:.1f}, {y:.1f}) within {radius:.0f}.",
            Py4GW.Console.MessageType.Warning,
        )
        return False

    Player.ChangeTarget(target_id)
    yield from Routines.Yield.wait(150)
    Player.Interact(target_id, False)

    deadline = time.time() + (timeout_ms / 1000.0)
    while time.time() < deadline:
        px, py = Player.GetXY()
        tx, ty = Agent.GetXY(target_id)
        dx = float(px) - float(tx)
        dy = float(py) - float(ty)
        if (dx * dx + dy * dy) <= (220.0 * 220.0):
            yield from Routines.Yield.wait(500)
            return True
        Player.ChangeTarget(target_id)
        Player.Interact(target_id, False)
        yield from Routines.Yield.wait(500)

    ConsoleLog(BOT_NAME, f"{display_name}: timeout waiting to reach/interact with encoded NPC.", Py4GW.Console.MessageType.Warning)
    return False


def _send_dialog_to_party_current_target(dialog_id: int, wait_ms: int = 3000) -> Generator:
    target = Player.GetTargetID()
    if target == 0:
        ConsoleLog(BOT_NAME, f"No target selected for dialog {dialog_id}.", Py4GW.Console.MessageType.Warning)
        return

    sender_email = Player.GetAccountEmail()
    accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
    for account in accounts:
        account_email = getattr(account, "AccountEmail", "")
        if not account_email:
            continue
        GLOBAL_CACHE.ShMem.SendMessage(
            sender_email,
            account_email,
            SharedCommandType.SendDialogToTarget,
            (target, dialog_id, 0, 0),
        )
    yield from Routines.Yield.wait(wait_ms)


def _take_beacon_of_droknar_blessing(x: float, y: float) -> Generator:
    success = yield from _interact_encoded_npc_near_xy(
        BEACON_OF_DROKNAR_ENCODED_NAMES,
        "Beacon of Droknar",
        x,
        y,
    )
    if not success:
        # Fallback keeps old behavior if encoded lookup is unavailable for any reason.
        yield from Routines.Yield.Agents.InteractWithAgentXY(x, y, timeout_ms=10000, tolerance=220.0)

    yield from Routines.Yield.wait(750)
    Player.SendDialog(DWARVEN_BLESSING_DIALOG)
    yield from _send_dialog_to_party_current_target(DWARVEN_BLESSING_DIALOG)
    yield from Routines.Yield.wait(1000)
    yield


def _send_precombat_prep_to_party(reason: str) -> None:
    """Ask multibox accounts to run the same spirit/shout prep used by CombatPrep."""
    sender_email = Player.GetAccountEmail()
    if not sender_email:
        return

    try:
        accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
    except Exception:
        accounts = []

    sent = 0
    for account in accounts:
        account_email = getattr(account, "AccountEmail", "")
        if not account_email or account_email == sender_email:
            continue

        for prep_type in (CombatPrepSkillsType.SpiritsPrep, CombatPrepSkillsType.ShoutsPrep):
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account_email,
                SharedCommandType.UseSkillCombatPrep,
                (prep_type, 0, 0, 0),
            )
        sent += 1

    if sent:
        ConsoleLog(
            BOT_NAME,
            f"[Mission Map Path] Pre-combat prep requested for {sent} account(s): {reason}.",
            Py4GW.Console.MessageType.Info,
        )


def _maybe_run_precombat_prep(step_name: str) -> None:
    global _last_precombat_prep_ms
    now_ms = int(time.time() * 1000)
    if now_ms - _last_precombat_prep_ms < _PRECOMBAT_PREP_COOLDOWN_MS:
        return
    _last_precombat_prep_ms = now_ms
    _send_precombat_prep_to_party(step_name)


def _snap_point_like_mission_map(raw_point: tuple[float, float], step_name: str) -> Generator:
    """Snap one route target the same way Mission Map+ right-click snap does."""
    yield from AutoPathing().load_pathing_maps()
    nav = AutoPathing().get_navmesh()

    point = (float(raw_point[0]), float(raw_point[1]))
    snapped = nav.find_nearest_reachable(point) if nav else None
    if snapped is None:
        ConsoleLog(
            BOT_NAME,
            f"[Mission Map Path] {step_name}: using raw point ({point[0]:.1f}, {point[1]:.1f}); navmesh snap unavailable.",
            Py4GW.Console.MessageType.Warning,
        )
        return point

    snapped_point = (float(snapped[0]), float(snapped[1]))
    if (abs(snapped_point[0] - point[0]) > 1.0) or (abs(snapped_point[1] - point[1]) > 1.0):
        ConsoleLog(
            BOT_NAME,
            f"[Mission Map Path] {step_name}: snapped ({point[0]:.1f}, {point[1]:.1f}) -> ({snapped_point[0]:.1f}, {snapped_point[1]:.1f}).",
            Py4GW.Console.MessageType.Info,
        )
    return snapped_point


def _is_player_dead() -> bool:
    try:
        return Agent.IsDead(Player.GetAgentID()) or Routines.Checks.Player.IsDead()
    except Exception:
        return False


def _is_party_alive_for_unstuck() -> bool:
    try:
        return not _is_player_dead() and not Routines.Checks.Party.IsPartyMemberDead()
    except Exception:
        return not _is_player_dead()


def _send_stuck_command_to_party(reason: str) -> None:
    ConsoleLog(BOT_NAME, f"[Mission Map Path] Stuck detected; sending /stuck ({reason}).", Py4GW.Console.MessageType.Warning)
    Player.SendChatCommand("stuck")

    sender_email = Player.GetAccountEmail()
    if not sender_email:
        return

    try:
        px, py = Player.GetXY()
        accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
        for account in accounts:
            account_email = getattr(account, "AccountEmail", "")
            if not account_email or account_email == sender_email:
                continue
            # There is no generic multibox chat-command message handler here; BruteForceUnstuck starts with /stuck
            # on the receiving account and then attempts light recovery if still blocked.
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account_email,
                SharedCommandType.BruteForceUnstuck,
                (float(px), float(py), 0, 0),
            )
    except Exception as exc:
        ConsoleLog(BOT_NAME, f"[Mission Map Path] Failed to send multibox /stuck recovery: {exc}", Py4GW.Console.MessageType.Warning)


def _wait_for_respawn_position_change(previous_pos: tuple[float, float], step_name: str) -> Generator:
    """Wait for dungeon-wipe respawn before rebuilding movement from the new current position."""
    ConsoleLog(
        BOT_NAME,
        f"[Mission Map Path] {step_name}: death detected; waiting for respawn before recalculating path.",
        Py4GW.Console.MessageType.Warning,
    )

    # Dungeon party wipes take roughly 10s to respawn.  Do not reuse the old
    # movement tree/path after that; wait until the player is alive and the
    # shrine moved us to a different position, then build a fresh navmesh path.
    start = time.time()
    min_wait_done = False
    position_changed = False
    while True:
        if (time.time() - start) >= 10.0:
            min_wait_done = True

        current_pos = Player.GetXY()
        if current_pos:
            dx = float(current_pos[0]) - float(previous_pos[0])
            dy = float(current_pos[1]) - float(previous_pos[1])
            position_changed = (dx * dx + dy * dy) >= (250.0 * 250.0)

        if min_wait_done and not _is_player_dead() and position_changed:
            ConsoleLog(
                BOT_NAME,
                f"[Mission Map Path] {step_name}: respawn confirmed at ({current_pos[0]:.1f}, {current_pos[1]:.1f}); recalculating path.",
                Py4GW.Console.MessageType.Info,
            )
            return

        # Failsafe: if the game reports alive but the position did not change
        # for an unusually long time, continue anyway with a fresh path from the
        # current position rather than leaving an old move command active.
        if (time.time() - start) >= 20.0 and not _is_player_dead():
            ConsoleLog(
                BOT_NAME,
                f"[Mission Map Path] {step_name}: respawn position change was not observed; recalculating path from current position anyway.",
                Py4GW.Console.MessageType.Warning,
            )
            return

        yield from Routines.Yield.wait(250)


def _new_mission_map_move_tree(
    snapped_x: float,
    snapped_y: float,
    timeout_ms: int = _MISSION_MAP_MOVE_TIMEOUT_MS,
) -> BehaviorTree:
    # One target, autopathing enabled. This matches Mission Map+ right-click
    # behavior: snap the clicked point to the navmesh, calculate a path from the
    # player's *current* position, then issue normal Player.Move commands along it.
    return BT.Movement.Move(snapped_x, snapped_y, timeout_ms=timeout_ms, log=False)


def _perpendicular_stuck_recovery_point(
    current_pos: tuple[float, float],
    target_pos: tuple[float, float],
    side: int,
) -> tuple[float, float] | None:
    current_x, current_y = float(current_pos[0]), float(current_pos[1])
    target_x, target_y = float(target_pos[0]), float(target_pos[1])
    dx = target_x - current_x
    dy = target_y - current_y
    distance = math.hypot(dx, dy)
    if distance < 1.0:
        return None

    midpoint_x = current_x + dx * 0.5
    midpoint_y = current_y + dy * 0.5
    perpendicular_x = -dy / distance * side
    perpendicular_y = dx / distance * side
    return (
        midpoint_x + perpendicular_x * _MISSION_MAP_STUCK_RECOVERY_OFFSET,
        midpoint_y + perpendicular_y * _MISSION_MAP_STUCK_RECOVERY_OFFSET,
    )


def _run_mission_map_stuck_recovery_detour(raw_point: tuple[float, float], step_name: str) -> Generator:
    snapped_x, snapped_y = yield from _snap_point_like_mission_map(raw_point, f"{step_name} stuck recovery")
    move_tree = _new_mission_map_move_tree(
        snapped_x,
        snapped_y,
        timeout_ms=_MISSION_MAP_STUCK_RECOVERY_TIMEOUT_MS,
    )
    start = time.time()
    while (time.time() - start) * 1000 < _MISSION_MAP_STUCK_RECOVERY_TIMEOUT_MS:
        state = BehaviorTree.Node._normalize_state(move_tree.tick())
        if state == BT.NodeState.SUCCESS:
            return True
        if state == BT.NodeState.FAILURE:
            return False
        yield from Routines.Yield.wait(100)
    return False


def _run_mission_map_move_to(raw_point: tuple[float, float], step_name: str) -> Generator:
    snapped_x, snapped_y = yield from _snap_point_like_mission_map(raw_point, step_name)
    move_tree = _new_mission_map_move_tree(snapped_x, snapped_y)
    retry_count = 0
    stuck_anchor_pos = Player.GetXY()
    stuck_anchor_time = time.time()
    last_stuck_command_time = 0.0
    stuck_recovery_side = 1
    while True:
        if _is_player_dead():
            death_pos = Player.GetXY()
            yield from _wait_for_respawn_position_change((float(death_pos[0]), float(death_pos[1])), step_name)
            move_tree = _new_mission_map_move_tree(snapped_x, snapped_y)
            retry_count = 0
            stuck_anchor_pos = Player.GetXY()
            stuck_anchor_time = time.time()
            last_stuck_command_time = 0.0

        current_pos = Player.GetXY()
        moved_dx = float(current_pos[0]) - float(stuck_anchor_pos[0])
        moved_dy = float(current_pos[1]) - float(stuck_anchor_pos[1])
        now = time.time()
        if (moved_dx * moved_dx + moved_dy * moved_dy) > (_STUCK_POSITION_RADIUS * _STUCK_POSITION_RADIUS):
            stuck_anchor_pos = current_pos
            stuck_anchor_time = now
        elif (
            (now - stuck_anchor_time) >= _STUCK_POSITION_SECONDS
            and (now - last_stuck_command_time) >= _STUCK_COMMAND_COOLDOWN_SECONDS
            and _is_party_alive_for_unstuck()
        ):
            _send_stuck_command_to_party(
                f"{step_name}; no position change > {_STUCK_POSITION_RADIUS:.0f} for {_STUCK_POSITION_SECONDS:.0f}s"
            )
            last_stuck_command_time = now
            yield from Routines.Yield.wait(_MISSION_MAP_STUCK_POST_COMMAND_WAIT_MS)

            current_pos = Player.GetXY()
            recovery_point = _perpendicular_stuck_recovery_point(
                (float(current_pos[0]), float(current_pos[1])),
                (snapped_x, snapped_y),
                stuck_recovery_side,
            )
            stuck_recovery_side *= -1
            if recovery_point:
                ConsoleLog(
                    BOT_NAME,
                    f"[Mission Map Path] {step_name}: trying stuck recovery detour "
                    f"({recovery_point[0]:.1f}, {recovery_point[1]:.1f}) before retrying original target.",
                    Py4GW.Console.MessageType.Info,
                )
                yield from _run_mission_map_stuck_recovery_detour(recovery_point, step_name)

            move_tree = _new_mission_map_move_tree(snapped_x, snapped_y)
            stuck_anchor_pos = Player.GetXY()
            stuck_anchor_time = time.time()
            continue

        pause_for_danger = _mission_map_danger_nearby()
        if pause_for_danger:
            _maybe_run_precombat_prep(step_name)

        move_tree.blackboard["PAUSE_MOVEMENT"] = pause_for_danger
        state = BehaviorTree.Node._normalize_state(move_tree.tick())
        if state == BT.NodeState.SUCCESS:
            yield
            return
        if state == BT.NodeState.FAILURE:
            retry_count += 1
            current_pos = Player.GetXY()
            ConsoleLog(
                BOT_NAME,
                f"[Mission Map Path] {step_name}: movement failed at ({raw_point[0]:.1f}, {raw_point[1]:.1f}); "
                f"retry {retry_count} from ({current_pos[0]:.1f}, {current_pos[1]:.1f}) with a fresh navmesh path.",
                Py4GW.Console.MessageType.Warning,
            )
            Player.Move(current_pos[0], current_pos[1])
            yield from Routines.Yield.wait(_MISSION_MAP_MOVE_RETRY_WAIT_MS)
            move_tree = _new_mission_map_move_tree(snapped_x, snapped_y)
            stuck_anchor_pos = Player.GetXY()
            stuck_anchor_time = time.time()
            continue
        yield from Routines.Yield.wait(100)


def AddMissionMapPath(
    points: list[tuple[float, float]],
    step_name: str,
) -> None:
    route = _normalize_route_points(points)
    if not route:
        bot.States.AddCustomState(_step_anchor, f"{step_name} (empty route)")
        return

    def _movement_state() -> Generator:
        total = len(route)
        for index, point in enumerate(route, start=1):
            yield from _run_mission_map_move_to(point, f"{step_name} {index}/{total}")

    bot.States.AddCustomState(_movement_state, step_name)

# ==================== CORE ROUTINE ====================
def farm_froggy_routine(bot: Botting) -> None:
    
    # ===== INITIAL CONFIGURATION =====
    # Register wipe callback
    bot.Events.OnPartyWipeCallback(lambda: OnPartyWipe(bot))
    

    
    # ===== START OF BOT =====
    bot.States.AddHeader("Startup - Widget Setup")
    bot.Properties.Enable("pause_on_danger")
    bot.States.AddCustomState(apply_widget_policy_step, "Apply widget policy")
    bot.States.AddCustomState(lambda: _gh_merchant_setup(leave_party=True), "GH Merchant Setup")
    bot.Templates.Aggressive()
    bot.Multibox.AbandonQuest(TEKKS_WAR_QUEST_ID)
    bot.States.AddHeader("Startup - Party Setup")
    bot.Events.OnPartyMemberBehindCallback(lambda: bot.Templates.Routines.OnPartyMemberBehind())
    bot.Events.OnPartyMemberInDangerCallback(lambda: bot.Templates.Routines.OnPartyMemberInDanger())
    bot.Events.OnPartyMemberDeadBehindCallback(lambda: bot.Templates.Routines.OnPartyMemberDeathBehind())
    bot.Multibox.KickAllAccounts()
    bot.States.AddCustomState(lambda: _coro_travel_random_district(GADDS_ENCAMPMENT), "Travel to Vlox's Falls")
    bot.States.AddCustomState(loop_marker, "Reset Post Merchant")
    bot.States.AddCustomState(lambda: _summon_and_invite_party(), "Initial Party Invite")
    bot.States.AddCustomState(lambda: _reenable_merchant_widgets(), "Re-enable widgets (all in Vlox's Falls)")
    bot.Multibox.RestockAllPcons()
    bot.Multibox.RestockConset()
    bot.Multibox.RestockResurrectionScroll(250)


    
    # ===== START OF LOOP =====
    bot.States.AddHeader("Run Loop")
    _ensure_ini_initialized()
    bot.Party.SetHardMode(_use_hard_mode)
    # Enable properties
    bot.Properties.Enable('hero_ai')
    bot.States.AddCustomState(_force_leader_hero_ai_combat, "Force leader HeroAI combat on")
    bot.States.AddCustomState(_step_anchor, "Reset farm")  # anchor for secure return on wipe    
    # ===== GO TO DUNGEON =====
    bot.Quest.AbandonQuest(TEKKS_QUEST_ID)
    bot.States.AddHeader("Go to Dungeon")
    bot.States.AddCustomState(lambda: _set_dungeon_looting(False, "running to dungeon"), "Disable looting while running to dungeon")
    bot.Templates.Aggressive()
    bot.Move.XYAndExitMap(-9451.37, -19766.40, target_map_id=SPARKFLY)
    bot.Wait.UntilOnExplorable()
 
 
    # First blessing immediately after zoning into Sparkfly.
    AddMissionMapPath([(-8950.0, -19843.0)], "Recorded route - Sparkfly blessing approach")
    bot.Interact.WithNpcAtXY(-8950.0, -19843.0)
    bot.Multibox.SendDialogToTarget(DWARVEN_BLESSING_DIALOG)
    bot.Wait.ForTime(4000)
    bot.States.AddCustomState(lambda: _use_precons_if_enabled("running", "after Sparkfly blessing"), "Use precons after Sparkfly blessing")

    # Recorded route to Tekks. Movement is executed like Mission Map+ right-click snap.
    path = [
    (-10787.0, -12984.0),
    (-7978.0, -11380.0),
    (-6779.0, -8893.0),
    (-4725.0, -5677.0),
    (-3590.0, -2898.0),
    (-349.0, 1100.0),
    (-313.0, 5633.0),
    (3682.0, 9598.0),
    (4888.0, 10325.0),
    (6348.0, 12176.0),
    (10731.0, 18283.0),
    (11540.0, 18946.0),
    (12404.0, 21935.0),
]
    AddMissionMapPath(path, "Recorded route - Sparkfly to Tekks")
    bot.Wait.UntilOutOfCombat()
    
    # ===== LOOP RESTART POINT =====
    bot.States.AddCustomState(loop_marker, "LOOP_RESTART_POINT")

    # Walk to tekks first with Mission Map style pathing, then interact if needed.
    AddMissionMapPath([(12500.0, 22648.0)], "Recorded route - final Tekks approach")
    bot.States.AddCustomState(lambda: _handle_tekks(bot), "tekks Quest Handler")

    # Enter the dungeon using the same Mission Map style movement.
    AddMissionMapPath(
        [
            (11676.01, 22685.0),
            (11562.77, 24059.0),
            (13097.0, 26393.0),
        ],
        "Recorded route - Tekks to dungeon portal",
    )

    bot.Wait.ForMapToChange(target_map_id=BOGROOT_L1)
    bot.States.AddCustomState(lambda: _set_dungeon_looting(True, "inside dungeon"), "Enable looting for dungeon levels")
    

    # =========================
    #           Level 1
    # =========================
    bot.States.AddHeader("Level 1 - Entry and Blessing")

    # Ensure quest state is Active and not Complete. Loops tekks interaction until this condition is met.
    bot.States.AddCustomState(lambda: _check_tekks_inside_dungeon(bot), "Check Quest State (inside dungeon)")
    bot.States.AddCustomState(_mark_run_start, "Mark Run Start")
    bot.States.AddCustomState(_take_dungeon_entry_snapshot, "Pre-Dungeon Snapshot (All Accounts)")

    # First blessing Level 1
    bot.States.AddCustomState(lambda: S_WhitelistModels(BOSS_KEY_MODEL_IDS), "Whitelist Boss Key")
    bot.States.AddCustomState(lambda: _use_precons_if_enabled("level1", "before Level 1 blessing"), "Use precons before L1 blessing")
    AddMissionMapPath([(19004.0, 7771.0)], "Recorded route - Level 1 blessing approach")
    bot.Wait.UntilOutOfCombat()
    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(19004.0, 7771.0), "Take Beacon of Droknar Blessing")

    bot.States.AddHeader("Level 1 - Secure Return Checkpoint 1")
    bot.States.AddCustomState(_step_anchor, "Secure return - L1")
    
    # Use consumables
    bot.States.AddCustomState(UseSummons, "Use Summons")
    bot.Templates.Aggressive()

    path_1 = [
    (16391.0, 8670.0),
    (11635.0, 6416.0),
    (9627.0, 7246.0),
    (6829.0, 5528.0),
    (4976.0, 1977.0),
    ]
    bot.Templates.Aggressive()
    bot.Wait.UntilOutOfCombat()
    AddMissionMapPath(path_1, "Recorded route - Level 1 first segment")

    bot.States.AddHeader("Level 1 - Secure Return Checkpoint 2")
    bot.States.AddCustomState(_step_anchor, "Secure return 2 - L1")
    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(4976.0, 1977.0), "Take Beacon of Droknar Blessing - L1 Mid")

    path_2= [
    (2359.0, -1466.0),
    (334.0, -1982.0),
    (-896.0, -4092.0),
    (-1289.0, -6259.0),
    (169.0, -8898.0),
    (1541.0, -10821.0),
    (1466.0, -14779.0),
    (7251.0, -17270.0),
    (7865.0, -19350.0),
    ]
    bot.Templates.Aggressive()
    AddMissionMapPath(path_2, "Recorded route - Level 1 second segment to exit")
    bot.Wait.UntilOutOfCombat()

    bot.States.AddHeader("Level 1 - Secure Return Checkpoint 3")
    bot.States.AddCustomState(_step_anchor, "Secure return 3 - L1")

    bot.Wait.ForMapToChange(target_map_name="Bogroot Growths (level 2)")
    bot.States.AddCustomState(_mark_l2_start, "Mark L2 Start")
    bot.Wait.ForTime(2000)

    # =========================
    #          Level 2
    # =========================

    bot.States.AddHeader("Level 2 - Entry and Blessing")
    AddMissionMapPath([(-11055.0, -5551.0)], "Recorded route - Level 2 entry blessing approach")
    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(-11055.0, -5551.0), "Take Beacon of Droknar Blessing - L2 Entry")
    bot.States.AddHeader("Level 2 - Secure Return Checkpoint")
    bot.States.AddCustomState(_step_anchor, "Secure return - L2")
    bot.States.AddCustomState(_reset_l2_boss_route_flag, "Reset L2 boss route flag")
    bot.States.AddCustomState(UseSummons, "Use Summons")
    bot.States.AddCustomState(lambda: _use_precons_if_enabled("level2", "after Level 2 blessing"), "Use precons after L2 blessing")
    bot.Templates.Aggressive()

    path_4 = [
        (-11147.0, -3052.0),
        (-11340.0, -1168.0),
        (-8825.0, 463.0),
        (-7128.0, 2972.0),
        (-5332.0, 3461.0),
        (-3847.0, 5041.0),
        (-2700.0, 5869.0),
        (-2815.0, 7132.0),
        (-2454.0, 8168.0),
        (-1220.0, 8012.0),
        (24.0, 9942.0),
        (-592.0, 11206.0),
    ]
    AddMissionMapPath(path_4, "Recorded route - Level 2 first route")
    bot.Wait.UntilOutOfCombat()

    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(-592.0, 11206.0), "Take Beacon of Droknar Blessing - L2 Mid")

    bot.States.AddHeader("Level 2 - Secure Return Checkpoint 2")
    bot.States.AddCustomState(_step_anchor, "Secure return 2 - L2")

    path_5 = [
        (-592.0, 11206.0),
        (2989.0, 12488.0),
        (3302.0, 13813.0),
        (6023.0, 13663.0),
        (5610.0, 11695.0),
        (7060.0, 9799.0),
        (8347.0, 5300.0),
        (8391.0, 4016.0),
    ]
    bot.Templates.Aggressive()
    AddMissionMapPath(path_5, "Recorded route - Level 2 second route")
    bot.Wait.UntilOutOfCombat()

    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(8391.0, 4016.0), "Take Beacon of Droknar Blessing - L2 Upper")

    bot.States.AddHeader("Level 2 - Secure Return Checkpoint 3")
    bot.States.AddCustomState(_step_anchor, "Secure return 3 - L2")

    path_6 = [
        (8391.0, 4016.0),
        (8355.0, 981.0),
        (10684.0, -3134.0),
        (10819.0, -5150.0),
        (12219.0, -6362.0),
        (17406.0, -6165.0),
    ]
    bot.Templates.Aggressive()
    AddMissionMapPath(path_6, "Recorded route - Level 2 boss lock approach")
    bot.Wait.UntilOutOfCombat()

    bot.States.AddHeader("Open Boss Door")
    bot.Interact.WithGadgetAtXY(17867.55, -6250.63, "Open Door")

    bot.States.AddHeader("Level 2 - Door Checkpoint")
    bot.States.AddCustomState(_step_anchor, "Secure return - L2 door")

    path_7 = [
        (17406.0, -6165.0),
        (18272.0, -8327.0),
        (17899.0, -9402.0),
        (16299.0, -10595.0),
        (16990.0, -11840.0),
        (19130.0, -12233.0),
    ]
    bot.Templates.Aggressive()
    AddMissionMapPath(path_7, "Recorded route - Level 2 boss blessing approach")
    bot.Wait.UntilOutOfCombat()

    bot.States.AddCustomState(lambda: _take_beacon_of_droknar_blessing(19130.0, -12233.0), "Take Beacon of Droknar Blessing - Before Boss")

    bot.States.AddHeader("Level 2 - Boss Checkpoint")
    bot.States.AddCustomState(_step_anchor, "Secure return - Boss")
    bot.States.AddCustomState(_set_l2_boss_route_flag, "Set L2 boss route flag")

    bot.States.AddHeader("Level 2 - Path to Boss")

    path_froggy = [
        (19130.0, -12233.0),
        (17800.0, -14121.0),
        (14588.0, -15174.0),
        (15579.0, -19111.0),
    ]
    bot.Templates.Aggressive()
    AddMissionMapPath(path_froggy, "Recorded route - Level 2 boss and chest approach")
    bot.States.AddCustomState(_record_run_end, "Record Run End")
    bot.States.AddHeader("Final Chest")

    AddMissionMapPath([BOGROOT_CHEST_POSITION], "Recorded route - final chest approach")
    bot.States.AddCustomState(open_BOGROOT_chest, "Open Chest (All Accounts)")
    bot.States.AddCustomState(_record_drops_after_loot, "Record Drop Stats After Loot")
    AddMissionMapPath([(15018.0, -17666.0)], "Recorded route - chest to quest reward")
    bot.States.AddCustomState(lambda: _collect_tekks_reward_in_dungeon(bot), "Collect Quest Reward (in dungeon)")
    # ===== NEXT RUN =====
    bot.Wait.ForMapToChange(target_map_name="Sparkfly Swamp")
    bot.States.AddCustomState(_gh_merchant_setup_if_inventory_full, "GH Merchant if inventory full")
    bot.States.AddCustomState(_gh_merchant_setup_for_alt_salvage_threshold, "GH Merchant if alt salvage kits are low")
    bot.States.AddCustomState(lambda: _handle_tekks(bot), "tekks Quest Handler")
    
    # ===== LOOP =====
    bot.States.JumpToStepName("LOOP_RESTART_POINT")
# ==================== CUSTOM HELPERS ====================


# --- Merchant Setup and Inventory Helpers ---

def _find_npc_xy_by_name(name_fragment: str, max_dist: float = 15000.0):
    """Find the nearest NPC whose display name contains name_fragment."""
    npcs = AgentArray.GetNPCMinipetArray()
    npcs = AgentArray.Filter.ByDistance(npcs, Player.GetXY(), max_dist)
    for npc_id in npcs:
        npc_name = Agent.GetNameByID(int(npc_id))
        if name_fragment.lower() in npc_name.lower():
            return Agent.GetXY(int(npc_id))
    return None


def _count_model_in_inventory(model_id: int) -> int:
    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)
    count = 0
    for item_id in item_array:
        if int(GLOBAL_CACHE.Item.GetModelID(item_id)) == int(model_id):
            count += max(1, int(GLOBAL_CACHE.Item.Properties.GetQuantity(item_id)))
    return count


def _account_key(email: str) -> str:
    return email.replace("@", "_at_").replace(".", "_")

def _display_email(key: str) -> str:
    """Reverse _account_key for display — converts storage key back to email format."""
    return key.replace("_at_", "@").replace("_", ".")

def _masked_email(key: str) -> str:
    """Return display email or a stable fake label if _scramble_accounts is enabled."""
    if not _scramble_accounts:
        return _char_names.get(key) or _display_email(key)
    all_keys = sorted(set(list(_froggy_drops.keys()) + list(_session_froggy.keys()) + list(_gb_drops.keys()) + list(_session_gb.keys())))
    idx = all_keys.index(key) + 1 if key in all_keys else 0
    return f"Player {idx}"


def _write_local_salvage_kit_count() -> None:
    from Py4GWCoreLib.enums_src.Model_enums import ModelID as _ModelID

    email = Player.GetAccountEmail()
    salvage_count = int(GLOBAL_CACHE.Inventory.GetModelCount(_ModelID.Salvage_Kit.value))
    _settings_ini.write_key(_ALT_SALVAGE_SECTION, _account_key(email), str(salvage_count))


def _request_alt_salvage_kit_counts() -> Generator:
    from Py4GWCoreLib.enums_src.Model_enums import ModelID as _ModelID
    salvage_kit_id = int(_ModelID.Salvage_Kit.value)

    my_email = Player.GetAccountEmail()
    alt_accounts = [acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData() if acc.AccountEmail != my_email]
    for acc in alt_accounts:
        reset_inventory_count(acc.AccountEmail, salvage_kit_id, salvage_kit_id)
        _settings_ini.write_key(_ALT_SALVAGE_SECTION, _account_key(acc.AccountEmail), str(-1))

    pending_accounts = alt_accounts
    max_attempts = max(1, _ALT_SALVAGE_POLL_MAX_TOTAL_MS // max(1, _ALT_SALVAGE_POLL_TIMEOUT_MS))
    for _attempt in range(max_attempts):
        if not pending_accounts:
            break

        for acc in pending_accounts:
            GLOBAL_CACHE.ShMem.SendMessage(
                my_email,
                acc.AccountEmail,
                SharedCommandType.InventoryQuery,
                (float(salvage_kit_id), float(salvage_kit_id), 0.0, 0.0),
                ("report_inventory_count",),
            )

        yield from Routines.Yield.wait(_ALT_SALVAGE_POLL_TIMEOUT_MS)

        still_pending = []
        for acc in pending_accounts:
            count = get_inventory_count(acc.AccountEmail, salvage_kit_id, salvage_kit_id)
            if count >= 0:
                _settings_ini.write_key(_ALT_SALVAGE_SECTION, _account_key(acc.AccountEmail), str(count))
            else:
                still_pending.append(acc)
        pending_accounts = still_pending

    if pending_accounts:
        pending_names = [acc.AgentData.CharacterName or acc.AccountEmail for acc in pending_accounts]
        ConsoleLog(
            BOT_NAME,
            f"[Merchant] No salvage count reply after {max_attempts} attempts ({_ALT_SALVAGE_POLL_MAX_TOTAL_MS} ms max) from: {', '.join(pending_names)}. Skipping them this check.",
            Py4GW.Console.MessageType.Warning,
        )


def _alts_need_salvage_restock() -> tuple[bool, list[str], list[str]]:
    my_email = Player.GetAccountEmail()
    ini_reader = IniHandler(_settings_ini_path)
    low_accounts: list[str] = []
    unknown_accounts: list[str] = []
    for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if acc.AccountEmail == my_email:
            continue
        count = ini_reader.read_int(_ALT_SALVAGE_SECTION, _account_key(acc.AccountEmail), -1)
        char_name = acc.AgentData.CharacterName or acc.AccountEmail
        if count < 0:
            unknown_accounts.append(char_name)
            continue
        if count < _ALT_SALVAGE_TRIGGER_THRESHOLD:
            low_accounts.append(f"{char_name} ({count})")
    return len(low_accounts) > 0, low_accounts, unknown_accounts


def _coro_sell_rare_mats_at_trader(x: float, y: float, model_ids: set[int]) -> Generator:
    """Sell rare material items (by model ID) to the trader at (x, y), one unit at a time.
    Bypasses SellMaterialsAtTrader which skips IsRareMaterial items."""
    yield from Routines.Yield.Movement.FollowPath([(x, y)])
    yield from Routines.Yield.wait(100)
    yield from Routines.Yield.Agents.InteractWithAgentXY(x, y)
    yield from Routines.Yield.wait(1000)

    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)
    sold_total = 0
    for item_id in item_array:
        if int(GLOBAL_CACHE.Item.GetModelID(item_id)) not in model_ids:
            continue
        stack_qty = int(GLOBAL_CACHE.Item.Properties.GetQuantity(item_id))
        while stack_qty > 0:
            quoted = yield from Routines.Yield.Merchant._wait_for_quote(
                GLOBAL_CACHE.Trading.Trader.RequestSellQuote, item_id,
                timeout_ms=750, step_ms=10)
            if quoted <= 0:
                break
            GLOBAL_CACHE.Trading.Trader.SellItem(item_id, quoted)
            new_qty = yield from Routines.Yield.Merchant._wait_for_stack_quantity_drop(
                item_id, stack_qty, timeout_ms=750, step_ms=10)
            if new_qty >= stack_qty:
                break
            sold_total += stack_qty - new_qty
            stack_qty = new_qty
    ConsoleLog(BOT_NAME, f"[Merchant] Sold {sold_total} rare material unit(s) at trader")


def _get_leftover_material_item_ids(batch_size: int = 10) -> list[int]:
    """Return item IDs of common (non-rare) material stacks with quantity < batch_size."""
    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)
    leftovers: list[int] = []
    for item_id in item_array:
        if not GLOBAL_CACHE.Item.Type.IsMaterial(item_id):
            continue
        if GLOBAL_CACHE.Item.Type.IsRareMaterial(item_id):
            continue
        qty = int(GLOBAL_CACHE.Item.Properties.GetQuantity(item_id))
        if 0 < qty < batch_size:
            leftovers.append(int(item_id))
    return leftovers


def _disable_widgets_on_alts_only(widget_names: tuple[str, ...]) -> Generator:
    if not widget_names:
        yield
        return

    my_email = Player.GetAccountEmail()
    for account in GLOBAL_CACHE.ShMem.GetAllAccountData():
        account_email = str(getattr(account, "AccountEmail", "") or "")
        if not account_email or account_email == my_email:
            continue
        for widget_name in widget_names:
            GLOBAL_CACHE.ShMem.SendMessage(
                my_email,
                account_email,
                SharedCommandType.DisableWidget,
                (0, 0, 0, 0),
                (widget_name, "", "", ""),
            )
    yield from Routines.Yield.wait(500)
def _get_material_item_ids_by_models(selected_models: set[int]) -> list[int]:
    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)
    result: list[int] = []
    for item_id in item_array:
        if not GLOBAL_CACHE.Item.Type.IsMaterial(item_id):
            continue
        if GLOBAL_CACHE.Item.Type.IsRareMaterial(item_id):
            continue
        model_id = int(GLOBAL_CACHE.Item.GetModelID(item_id))
        if model_id in selected_models:
            result.append(int(item_id))
    return result


def _coro_deposit_crafting_materials_to_storage(selected_models: set[int]) -> Generator:
    if not selected_models:
        yield
        return
    if not GLOBAL_CACHE.Inventory.IsStorageOpen():
        GLOBAL_CACHE.Inventory.OpenXunlaiWindow()
        yield from Routines.Yield.wait(1000)
    if not GLOBAL_CACHE.Inventory.IsStorageOpen():
        ConsoleLog(BOT_NAME, "[Merchant] Storage not open; skipping crafting material deposit", Py4GW.Console.MessageType.Warning)
        yield
        return

    item_ids = _get_material_item_ids_by_models(selected_models)
    if not item_ids:
        ConsoleLog(BOT_NAME, "[Merchant] No crafting materials to deposit")
        yield
        return

    for item_id in item_ids:
        GLOBAL_CACHE.Inventory.DepositItemToStorage(item_id)
        yield from Routines.Yield.wait(40)

    ConsoleLog(BOT_NAME, f"[Merchant] Deposited {len(item_ids)} crafting material stack(s) to storage")
    yield


_SCROLL_MODEL_IDS = {5594, 5595, 5611, 5853, 5975, 5976, 21233}
_SCROLL_MODEL_FILTER = "5594,5595,5611,5853,5975,5976,21233"


def _coro_sell_scrolls(mx: float, my: float) -> Generator:
    """Sell XP/insight scrolls to the GH merchant."""
    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)
    sell_ids = [int(item_id) for item_id in item_array
                if int(GLOBAL_CACHE.Item.GetModelID(item_id)) in _SCROLL_MODEL_IDS]
    if not sell_ids:
        ConsoleLog(BOT_NAME, "[Merchant] No scrolls to sell in bags 1-4")
        storage_hits = [(mid, GLOBAL_CACHE.Inventory.GetModelCountInStorage(mid))
                        for mid in _SCROLL_MODEL_IDS]
        storage_hits = [(mid, cnt) for mid, cnt in storage_hits if cnt > 0]
        if storage_hits:
            ConsoleLog(BOT_NAME, f"[Merchant] WARNING: scrolls found in STORAGE (InventoryPlus deposited them): {storage_hits}")
        yield
        return
    for item_id in sell_ids:
        val = GLOBAL_CACHE.Item.Properties.GetValue(item_id)
        qty = GLOBAL_CACHE.Item.Properties.GetQuantity(item_id)
        mid = GLOBAL_CACHE.Item.GetModelID(item_id)
        ConsoleLog(BOT_NAME, f"[Merchant] Scroll queued: item_id={item_id} model={mid} qty={qty} value={val}")
    yield from bot.Move._coro_xy_and_interact_npc(mx, my, "GH Merchant (scrolls)")
    yield from Routines.Yield.wait(1200)
    ConsoleLog(BOT_NAME, f"[Merchant] Selling {len(sell_ids)} scroll(s) at merchant")
    yield from Routines.Yield.Merchant.SellItems(sell_ids, log=True)
    yield from Routines.Yield.wait(300)


def _merchant_rules_widget_enabled() -> bool:
    widget_handler = get_widget_handler()
    for widget_name in ("Merchant Rules", "MerchantRules"):
        try:
            if widget_handler.is_widget_enabled(widget_name):
                return True
        except Exception:
            continue
    return False


def _get_merchant_rules_widget_instance():
    widget_handler = get_widget_handler()
    for widget_name in ("Merchant Rules", "MerchantRules"):
        widget_info = widget_handler.get_widget_info(widget_name)
        if not widget_info or not getattr(widget_info, "enabled", False):
            continue
        widget_instance = getattr(getattr(widget_info, "module", None), "WIDGET_INSTANCE", None)
        if widget_instance is not None:
            return widget_instance
    return None


def _run_merchant_rules_execute_here(stage_name: str = "GH merchant") -> Generator[Any, Any, bool]:
    """Run Merchant Rules if the widget is enabled; returns True when we attempted it."""
    if not _merchant_rules_widget_enabled():
        return False

    request_id = f"froggy-{int(time.time() * 1000)}"
    my_email = Player.GetAccountEmail()
    refs: list[tuple[str, int]] = []
    for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
        account_email = getattr(acc, "AccountEmail", "")
        if not account_email or account_email == my_email:
            continue
        msg_index = int(
            GLOBAL_CACHE.ShMem.SendMessage(
                my_email,
                account_email,
                SharedCommandType.MerchantRules,
                (3.0, 0.0, 0.0, 0.0),  # Merchant Rules execute opcode
                (request_id, f"{stage_name} execute", "", ""),
            )
        )
        if msg_index >= 0:
            refs.append((account_email, msg_index))

    widget = _get_merchant_rules_widget_instance()
    if widget is not None and callable(getattr(widget, "_execute_now", None)):
        ConsoleLog(BOT_NAME, "[Merchant] Merchant Rules enabled — executing rules for leader/alts.", Py4GW.Console.MessageType.Info)
        yield from widget._execute_now(local_only=True, exclude_consumable_crafter=True)
    else:
        ConsoleLog(BOT_NAME, "[Merchant] Merchant Rules enabled but widget instance unavailable for leader.", Py4GW.Console.MessageType.Warning)

    deadline = time.monotonic() + 60.0
    pending = {(email, idx): None for email, idx in refs}
    while pending and time.monotonic() < deadline:
        completed: list[tuple[str, int]] = []
        for account_email, msg_index in list(pending.keys()):
            message = GLOBAL_CACHE.ShMem.GetInbox(msg_index)
            is_same_message = (
                bool(getattr(message, "Active", False))
                and str(getattr(message, "ReceiverEmail", "") or "") == account_email
                and str(getattr(message, "SenderEmail", "") or "") == my_email
                and int(getattr(message, "Command", -1)) == int(SharedCommandType.MerchantRules)
            )
            if not is_same_message:
                completed.append((account_email, msg_index))
        for key in completed:
            pending.pop(key, None)
        if pending:
            yield from Routines.Yield.wait(100)

    if pending:
        pending_accounts = ", ".join(sorted({email for email, _ in pending}))
        ConsoleLog(BOT_NAME, f"[Merchant] Merchant Rules timeout for: {pending_accounts}", Py4GW.Console.MessageType.Warning)

    return True


def _coro_sell_nonsalvageable_golds(mx: float, my: float) -> Generator:
    """Identify and sell all non-FROGGY gold items to the GH merchant."""
    bag_list = GLOBAL_CACHE.ItemArray.CreateBagList(1, 2, 3, 4)
    item_array = GLOBAL_CACHE.ItemArray.GetItemArray(bag_list)

    gold_ids: list[int] = []
    unid_gold_ids: list[int] = []
    for item_id in item_array:
        model_id = int(GLOBAL_CACHE.Item.GetModelID(item_id))
        if model_id in FROGGY_MODEL_IDS:
            continue
        _, rarity = GLOBAL_CACHE.Item.Rarity.GetRarity(item_id)
        if rarity != "Gold":
            continue
        gold_ids.append(int(item_id))
        if not GLOBAL_CACHE.Item.Usage.IsIdentified(item_id):
            unid_gold_ids.append(int(item_id))

    if unid_gold_ids:
        ConsoleLog(BOT_NAME, f"[Merchant] Identifying {len(unid_gold_ids)} gold item(s) before selling")
        yield from Routines.Yield.Items.IdentifyItems(unid_gold_ids, log=True)
        yield from Routines.Yield.wait(500)

    sell_ids = [
        int(item_id)
        for item_id in gold_ids
        if GLOBAL_CACHE.Item.Usage.IsIdentified(item_id)
        and int(GLOBAL_CACHE.Item.GetModelID(item_id)) not in FROGGY_MODEL_IDS
    ]
    if not sell_ids:
        ConsoleLog(BOT_NAME, "[Merchant] No identified non-FROGGY gold items to sell")
        yield
        return
    yield from bot.Move._coro_xy_and_interact_npc(mx, my, "GH Merchant (gold items)")
    yield from Routines.Yield.wait(1200)
    ConsoleLog(BOT_NAME, f"[Merchant] Selling {len(sell_ids)} non-FROGGY gold item(s) at merchant")
    yield from Routines.Yield.Merchant.SellItems(sell_ids, log=True)
    yield from Routines.Yield.wait(300)


_MERCHANT_MANAGED_WIDGETS = ("InventoryPlus", "Inventory Plus")
_PRETRAVEL_DISABLE_WIDGETS = _MERCHANT_MANAGED_WIDGETS  # always disabled while this bot is running


def _disable_merchant_widgets() -> Generator:
    """Disable InventoryPlus on leader + all alts during GH merchant ops."""
    from Py4GWCoreLib.py4gwcorelib_src.WidgetManager import get_widget_handler as _get_wh
    ConsoleLog(BOT_NAME, "[Merchant] Disabling managed widgets on all accounts")
    wh = _get_wh()
    for name in _MERCHANT_MANAGED_WIDGETS:
        wh.disable_widget(name)
    _my_email = Player.GetAccountEmail()
    for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if acc.AccountEmail != _my_email:
            for name in _MERCHANT_MANAGED_WIDGETS:
                GLOBAL_CACHE.ShMem.SendMessage(
                    _my_email, acc.AccountEmail,
                    SharedCommandType.DisableWidget, (0, 0, 0, 0), (name, "", "", ""),
                )
    ConsoleLog(BOT_NAME, f"[Merchant] Disabled {_MERCHANT_MANAGED_WIDGETS} on all accounts")
    yield

def _move_to(x: float, y: float, tolerance: float = 180.0, max_tries: int = 60):
    Player.Move(x, y)

    for _ in range(max_tries):
        px, py = Player.GetXY()
        dist = Utils.Distance((px, py), (x, y))

        if dist <= tolerance:
            return True

        yield from Routines.Yield.wait(100)

    return False


def _wait_for_map(map_name: str, max_tries: int = 120):
    for _ in range(max_tries):
        if Map.GetMapName() == map_name:
            return True
        yield from Routines.Yield.wait(500)
    return False

# --- Quest State and tekks Interaction ---

def _tekks_quest_state() -> str:
    """Returns 'none' (not in log), 'active' (in progress), or 'complete' (reward ready)."""
    quest_ids = Quest.GetQuestLogIds()
    if TEKKS_QUEST_ID not in quest_ids:
        return "none"
    if Quest.IsQuestCompleted(TEKKS_QUEST_ID):
        return "complete"
    return "active"

def _handle_tekks(bot: Botting) -> Generator:
    """
    Unified tekks handler. Checks quest state and acts accordingly.
    Caller is responsible for moving the bot to tekks's position first.
      active   -> skip, proceed to dungeon
      complete -> collect reward (one dialog per map load; accept deferred to next visit)
      none     -> accept quest
    """
    state = _tekks_quest_state()
    ConsoleLog(BOT_NAME, f"[tekks] Quest state: {state}", log=True)

    if state == "active":
        ConsoleLog(BOT_NAME, "[tekks] Quest active — proceeding to dungeon", log=True)
        yield
        return

    if state == "complete":
        ConsoleLog(BOT_NAME, "[tekks] Collecting reward", log=True)
        ok = yield from _interact_with_tekks(bot, TEKKS_QUEST_REWARD_DIALOG)
        if not ok:
            ConsoleLog(BOT_NAME, "[tekks] Reward interaction failed", log=True)
        ConsoleLog(BOT_NAME, "[tekks] Reward collected — quest accept deferred to next map load", log=True)
        yield
        return

    if state == "none" :
        ConsoleLog(BOT_NAME, "[tekks] Accepting quest", log=True)
    ok = yield from _interact_with_tekks(bot, TEKKS_QUEST_TAKE_DIALOG)
    if not ok:
        ConsoleLog(BOT_NAME, "[tekks] Accept quest failed", log=True)
        yield
        return

    ConsoleLog(BOT_NAME, "[tekks] Handler complete", log=True)
    yield

def _collect_tekks_reward_in_dungeon(bot: Botting) -> Generator:
    
    ConsoleLog(BOT_NAME, "[tekks] Collecting reward inside dungeon", log=True)
    
    bot.Wait.ForTime(4000)
    ok = yield from _interact_with_tekks(bot, TEKKS_QUEST_REWARD_DIALOG)
    bot.Wait.ForTime(4000)
    
    if not ok:
        ConsoleLog(BOT_NAME, "[tekks] In-dungeon reward collection failed — will retry in Arbor Bay", log=True)
    yield

def _check_tekks_inside_dungeon(bot: Botting) -> Generator:
    """
    Inside dungeon check. Loops until the quest is confirmed active or
    max retries are exhausted (hard stop).
      active   -> nothing to do
      none     -> exit dungeon, handle tekks, re-enter, re-check
      complete -> exit dungeon, handle tekks, re-enter, re-check
    """
    _max_attempts = 3
    for _attempt in range(_max_attempts):
        state = _tekks_quest_state()
        ConsoleLog(BOT_NAME, f"[tekks] Inside dungeon state: {state} (attempt {_attempt + 1}/{_max_attempts})", log=True)

        if state == "active":
            yield
            return

        ConsoleLog(BOT_NAME, f"[tekks] Quest '{state}' inside dungeon — exiting to Arbor Bay", log=True)

        yield from Routines.Yield.Movement.FollowPath([(-15650.00, 8900.00)])

        ok = yield from _wait_for_map("Arbor Bay")
        if not ok:
            ConsoleLog(BOT_NAME, "[tekks] Failed to return to Arbor Bay", Py4GW.Console.MessageType.Warning)
            continue

        # Give the map time to fully load before attempting pathfinding
        yield from Routines.Yield.wait(10000)

        ConsoleLog(BOT_NAME, "[tekks] Back in Arbor Bay — moving to tekks", log=True)
        tekks_x, tekks_y = TEKKS_POSITION
        yield from Routines.Yield.Movement.FollowPath([
            (10218.0, -18864.0),
            (12056, -17882),
        ], stop_on_party_wipe=False)

        yield from _handle_tekks(bot)

        # Re-enter the dungeon so Level 1 routing executes on the correct map
        ConsoleLog(BOT_NAME, "[tekks] Re-entering dungeon", log=True)
        yield from Routines.Yield.Movement.FollowPath([
            (10218.0, -18864.0),
            (9519.0,  -19968.0),
            (9240.07, -20260.95),
        ], stop_on_party_wipe=False)

        ok = yield from wait_for_map_change(BOGROOT_L1, 60)
        if not ok:
            ConsoleLog(BOT_NAME, "[tekks] Failed to re-enter SoO Level 1 — retrying", Py4GW.Console.MessageType.Warning)
            continue

        yield from Routines.Yield.wait(2000)
        # Loop back to re-check quest state at the top

    # Exhausted all attempts — quest never became active
    ConsoleLog(BOT_NAME, f"[HARD STOP] tekks quest never became active after {_max_attempts} attempts — stopping bot.", Py4GW.Console.MessageType.Error)
    bot.Stop()
    yield

def find_nearest_npc_by_name(name_fragment: str, max_dist: float = 2000.0) -> int:
    """Find nearest NPC whose name contains name_fragment."""
    player_pos = Player.GetXY()

    npcs = AgentArray.GetNPCMinipetArray()
    npcs = AgentArray.Filter.ByDistance(npcs, player_pos, max_dist)
    npcs = AgentArray.Sort.ByDistance(npcs, player_pos)

    for npc_id in npcs:
        npc_id = int(npc_id)

        try:
            npc_name = Agent.GetNameByID(npc_id)
        except Exception:
            continue

        if name_fragment.lower() in npc_name.lower():
            return npc_id

    return 0

def _interact_with_tekks(bot: Botting, dialog_id: int, tolerance: float = 220.0, max_move_retries: int = 10):
    npc_name = "Tekks"

    # Retry a few times in case the agent list hasn't fully loaded yet
    agent_id = 0
    for _retry in range(5):
        agent_id = find_nearest_npc_by_name(npc_name, 5000.0)
        if agent_id:
            break
        yield from Routines.Yield.wait(500)

    if not agent_id:
        ConsoleLog(BOT_NAME, f"[tekks] {npc_name} not found nearby", log=True)
        return False

    # Log initial position
    x, y = Agent.GetXY(agent_id)
    px, py = Player.GetXY()
    dx = x - px
    dy = y - py
    distance = (dx * dx + dy * dy) ** 0.5

    ConsoleLog(
        BOT_NAME,
        f"[tekks] Found {npc_name} at ({x:.0f},{y:.0f}) dist={distance:.0f} agent_id={agent_id}",
        log=True
    )

    # Retry movement several times
    reached = False
    for attempt in range(1, max_move_retries + 1):
        if not Agent.IsLiving(agent_id):
            ConsoleLog(BOT_NAME, "[tekks] Tekks is no longer valid/alive", log=True)
            return False

        # Refresh NPC position in case it shifted slightly
        x, y = Agent.GetXY(agent_id)

        ConsoleLog(
            BOT_NAME,
            f"[tekks] Move attempt {attempt}/{max_move_retries} toward ({x:.0f},{y:.0f})",
            log=True
        )

        ok = yield from _move_to(x, y, tolerance=tolerance)
        if ok:
            reached = True
            break

        # Fallback: direct move once before retrying
        ConsoleLog(BOT_NAME, f"[tekks] _move_to failed, fallback Player.Move to ({x:.0f},{y:.0f})", log=True)
        Player.Move(x, y)
        yield from Routines.Yield.wait(1000)

    if not reached:
        ConsoleLog(BOT_NAME, "[tekks] Impossible to approach tekks after retries", log=True)
        return False

    Player.ChangeTarget(agent_id)
    yield from Routines.Yield.wait(800)
    Player.Interact(agent_id)
    yield from Routines.Yield.wait(800)
    Player.SendDialog(dialog_id)
    yield from Routines.Yield.wait(1500)

    # Dispatch the same dialog to all alt accounts
    sender_email = Player.GetAccountEmail()
    for account in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if account.AccountEmail != sender_email:
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account.AccountEmail,
                SharedCommandType.SendDialogToTarget,
                (agent_id, dialog_id, 0, 0)
            )

    yield from Routines.Yield.wait(1500)
    return True

L2_BOSS_ROUTE_UNLOCKED = False

def _reset_l2_boss_route_flag() -> Generator:
    global L2_BOSS_ROUTE_UNLOCKED
    L2_BOSS_ROUTE_UNLOCKED = False
    ConsoleLog(BOT_NAME, "[L2] Boss route unlocked = False")
    yield


def _set_l2_boss_route_flag() -> Generator:
    global L2_BOSS_ROUTE_UNLOCKED
    L2_BOSS_ROUTE_UNLOCKED = True
    ConsoleLog(BOT_NAME, "[L2] Boss route unlocked = True")
    yield


def _disable_inventoryplus_pretravel() -> Generator:
    """Disable InventoryPlus on leader + alts BEFORE GH travel, so InventoryPlus cannot
    run its auto-deposit cycle when accounts enter GH (which would send scrolls to storage)."""
    from Py4GWCoreLib.py4gwcorelib_src.WidgetManager import get_widget_handler as _get_wh
    ConsoleLog(BOT_NAME, "[Merchant] Pre-travel: disabling InventoryPlus on all accounts")
    wh = _get_wh()
    for name in _PRETRAVEL_DISABLE_WIDGETS:
        wh.disable_widget(name)
    _my_email = Player.GetAccountEmail()
    for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if acc.AccountEmail != _my_email:
            for name in _PRETRAVEL_DISABLE_WIDGETS:
                GLOBAL_CACHE.ShMem.SendMessage(
                    _my_email, acc.AccountEmail,
                    SharedCommandType.DisableWidget, (0, 0, 0, 0), (name, "", "", ""),
                )
    ConsoleLog(BOT_NAME, "[Merchant] Pre-travel: InventoryPlus disabled — waiting 1.5s for alts to process")
    yield from Routines.Yield.wait(1500)


def _reenable_merchant_widgets() -> Generator:
    """Historical hook name; InventoryPlus must remain disabled while this bot runs."""
    yield from _disable_merchant_widgets()


def _gh_merchant_setup(leave_party: bool = True) -> Generator:
    """Travel to Guild Hall (all accounts via SharedMemory), restock kits, sell materials,
    sell leftover stacks and optionally buy ectos. Mirrors the FoW modular bot pattern."""
    from Py4GWCoreLib.enums_src.Model_enums import ModelID as _ModelID

    _ensure_ini_initialized()
    if not _merchant_enabled:
        yield
        return

    _my_email = Player.GetAccountEmail()

    def _dispatch_to_alts(command, params, extra_data=("", "", "", "")) -> list[tuple[str, int]]:
        refs: list[tuple[str, int]] = []
        for _acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
            if _acc.AccountEmail != _my_email:
                msg_index = int(
                    GLOBAL_CACHE.ShMem.SendMessage(_my_email, _acc.AccountEmail, command, params, extra_data)
                )
                refs.append((_acc.AccountEmail, msg_index))
        return refs

    def _wait_for_alt_dispatch_completion(
        stage_name: str,
        message_refs: list[tuple[str, int]],
        command,
        timeout_ms: int = 30_000,
    ):
        if not message_refs:
            return
        pending: dict[tuple[str, int], None] = {
            (acc_email, msg_index): None
            for acc_email, msg_index in message_refs
            if int(msg_index) >= 0
        }
        if not pending:
            return
        deadline = time.monotonic() + (max(0, int(timeout_ms)) / 1000.0)
        while pending and time.monotonic() < deadline:
            completed: list[tuple[str, int]] = []
            for acc_email, msg_index in list(pending.keys()):
                message = GLOBAL_CACHE.ShMem.GetInbox(msg_index)
                is_same_message = (
                    bool(getattr(message, "Active", False))
                    and str(getattr(message, "ReceiverEmail", "") or "") == acc_email
                    and str(getattr(message, "SenderEmail", "") or "") == _my_email
                    and int(getattr(message, "Command", -1)) == int(command)
                )
                if not is_same_message:
                    completed.append((acc_email, msg_index))
            for key in completed:
                pending.pop(key, None)
            if pending:
                yield from Routines.Yield.wait(50)
        if pending:
            pending_accounts = ", ".join(sorted({email for email, _ in pending}))
            ConsoleLog(
                BOT_NAME,
                f"[Merchant] {stage_name}: timeout waiting for alt completion after {timeout_ms} ms. Pending: {pending_accounts}",
                Py4GW.Console.MessageType.Warning,
            )

    # —— Step 0 (startup only): Leave current party on all accounts ————————————
    if leave_party:
        ConsoleLog(BOT_NAME, "[Merchant] Leaving party on all accounts before GH travel")
        for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
            if acc.AccountEmail != _my_email:
                GLOBAL_CACHE.ShMem.SendMessage(_my_email, acc.AccountEmail, SharedCommandType.LeaveParty, (0, 0, 0, 0), ("", "", "", ""))
        GLOBAL_CACHE.Party.LeaveParty()
        yield from Routines.Yield.wait(2000)

    # —— Pre-travel: Disable InventoryPlus BEFORE GH entry so its auto-deposit cycle
    #    cannot send scrolls (or other items) to storage when accounts enter GH. ——
    yield from _disable_inventoryplus_pretravel()

    # —— Step 1: Send ALL accounts to their own Guild Hall ———————————————————
    # Snapshot alt count BEFORE dispatching travel — alts temporarily drop out of
    # ShMem during map transitions so the count must be captured while everyone
    # is still fully settled in Vlox's Fall.
    _expected_gh_alts = len([
        acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData()
        if acc.AccountEmail != _my_email
    ])
    ConsoleLog(BOT_NAME, "[Merchant] Dispatching GH travel to all accounts")
    _gh_refs = _dispatch_to_alts(SharedCommandType.TravelToGuildHall, (0, 0, 0, 0))
    if not Map.IsGuildHall():
        Map.TravelGH()
    yield from _wait_for_alt_dispatch_completion("travel_gh", _gh_refs, SharedCommandType.TravelToGuildHall, timeout_ms=10_000)

    # Wait for leader to arrive at GH
    _gh_deadline = time.time() + 30
    while not Map.IsGuildHall() and time.time() < _gh_deadline:
        yield from Routines.Yield.wait(500)

    if not Map.IsGuildHall():
        ConsoleLog(BOT_NAME, "[Merchant] Failed to reach Guild Hall — skipping merchant step")
        yield
        return

    # Wait for all alts to arrive at GH (match leader's map ID)
    _gh_map = int(Map.GetMapID())
    _arrival_deadline = time.time() + 60
    while time.time() < _arrival_deadline:
        _accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
        _in_gh = sum(
            1 for acc in _accounts
            if acc.AccountEmail != _my_email and int(acc.AgentData.Map.MapID) == _gh_map
        )
        if _in_gh >= _expected_gh_alts:
            ConsoleLog(BOT_NAME, f"[Merchant] All {_expected_gh_alts} alt(s) arrived at GH")
            break
        ConsoleLog(BOT_NAME, f"[Merchant] {_in_gh}/{_expected_gh_alts} alt(s) at GH — waiting")
        yield from Routines.Yield.wait(500)
    else:
        _accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
        _in_gh = sum(
            1 for acc in _accounts
            if acc.AccountEmail != _my_email and int(acc.AgentData.Map.MapID) == _gh_map
        )
        ConsoleLog(BOT_NAME, f"[Merchant] GH arrival timeout — {_in_gh}/{_expected_gh_alts} alts at GH. Proceeding.", Py4GW.Console.MessageType.Warning)

    # wait for Merchant NPC to spawn (handles fresh GH instances)
    _npc_deadline = time.time() + 20.0
    while _find_npc_xy_by_name("Merchant") is None:
        if time.time() > _npc_deadline:
            ConsoleLog(BOT_NAME, "[Merchant] Merchant NPC not found after 20s — proceeding anyway", Py4GW.Console.MessageType.Warning)
            break
        yield from Routines.Yield.wait(500)

    # —— Disable InventoryPlus on all accounts during merchant ops ——
    yield from _disable_merchant_widgets()

    # —— Step 2: Find NPC coordinates ——————————————————————————————————————————
    _RARE_MAT_MODELS = {935, 936}  # Diamond=935, Onyx Gemstone=936
    _RARE_MAT_FILTER  = "935,936"  # encoded for ShMem dispatch
    _CRAFTING_MAT_MODELS = {
        int(_ModelID.Pile_Of_Glittering_Dust.value),
        int(_ModelID.Bone.value),
        int(_ModelID.Iron_Ingot.value),
        int(_ModelID.Feather.value),
        int(_ModelID.Plant_Fiber.value),
    }
    _CRAFTING_MAT_FILTER = ",".join(str(mid) for mid in sorted(_CRAFTING_MAT_MODELS))

    merchant_xy   = _find_npc_xy_by_name("Merchant")
    mat_xy        = _find_npc_xy_by_name("Material Trader") if _merchant_sell_materials else None
    rare_xy       = _find_npc_xy_by_name("Rare") if (_merchant_buy_ectos or _merchant_sell_rare_mats) else None

    merchant_rules_ran = yield from _run_merchant_rules_execute_here("Froggy GH merchant")
    if not merchant_rules_ran:
        ConsoleLog(
            BOT_NAME,
            "[Merchant] Merchant Rules is not enabled/available; skipping all sell/salvage/storage cleanup and only restocking kits.",
            Py4GW.Console.MessageType.Warning,
        )

    # Item selling/salvage/storage cleanup is intentionally owned by Merchant Rules only.
    # The Frog bot keeps only GH travel + kit restock here.
    custom_cleanup_enabled = False

    # —— Step 2.5: Store consumable crafting mats before trader sales (leader + alts)
    if custom_cleanup_enabled and _merchant_store_consumable_materials:
        ConsoleLog(BOT_NAME, "[Merchant] Depositing consumable crafting materials to storage on all accounts")
        deposit_refs = _dispatch_to_alts(
            SharedCommandType.MerchantMaterials,
            (0, 0, 0, 0),
            ("deposit", _CRAFTING_MAT_FILTER, "", "0"),
        )
        yield from _coro_deposit_crafting_materials_to_storage(_CRAFTING_MAT_MODELS)
        yield from _wait_for_alt_dispatch_completion("deposit_materials", deposit_refs, SharedCommandType.MerchantMaterials)

    # —— Step 3: Sell materials at trader (leader + alts) —————————————————————
    if custom_cleanup_enabled and _merchant_sell_materials:
        if mat_xy:
            tmx, tmy = mat_xy
            ConsoleLog(BOT_NAME, f"[Merchant] Dispatching sell_materials to alts, trader at ({tmx:.0f}, {tmy:.0f})")
            sell_mat_refs = _dispatch_to_alts(
                SharedCommandType.MerchantMaterials,
                (tmx, tmy, 0, 0),
                ("sell", "", "", ""),
            )
            ConsoleLog(BOT_NAME, "[Merchant] Selling materials at trader (leader)")
            yield from Routines.Yield.Merchant.SellMaterialsAtTrader(tmx, tmy)
            yield from _wait_for_alt_dispatch_completion("sell_materials", sell_mat_refs, SharedCommandType.MerchantMaterials)
        else:
            ConsoleLog(BOT_NAME, "[Merchant] No Material Trader NPC found")

        # —— Step 4: Sell leftover stacks < 10 to regular merchant (leader + alts)
        if merchant_xy:
            mx, my = merchant_xy
            ConsoleLog(BOT_NAME, "[Merchant] Dispatching sell_merchant_leftovers to alts")
            leftover_refs = _dispatch_to_alts(
                SharedCommandType.MerchantMaterials,
                (mx, my, 0, 0),
                ("sell_merchant_leftovers", "", "10", ""),
            )
            leftover_ids = _get_leftover_material_item_ids()
            if leftover_ids:
                ConsoleLog(BOT_NAME, f"[Merchant] Selling {len(leftover_ids)} leftover stacks (leader)")
                yield from bot.Move._coro_xy_and_interact_npc(mx, my, "GH Merchant (leftovers)")
                yield from Routines.Yield.wait(1200)
                yield from Routines.Yield.Merchant.SellItems(leftover_ids, log=True)
                yield from Routines.Yield.wait(300)
            yield from _wait_for_alt_dispatch_completion(
                "sell_merchant_leftovers",
                leftover_refs,
                SharedCommandType.MerchantMaterials,
            )

    # —— Step 5: Legacy gold selling disabled; Merchant Rules owns sell/keep/salvage logic. ——
    if custom_cleanup_enabled and merchant_xy:
        mx, my = merchant_xy
        ConsoleLog(BOT_NAME, "[Merchant] Dispatching sell_nonsalvageable_golds to alts")
        sell_gold_refs = _dispatch_to_alts(
            SharedCommandType.MerchantMaterials,
            (mx, my, 0, 0),
            ("sell_nonsalvageable_golds", "", "", ""),
        )
        yield from _coro_sell_nonsalvageable_golds(mx, my)
        yield from _wait_for_alt_dispatch_completion(
            "sell_nonsalvageable_golds",
            sell_gold_refs,
            SharedCommandType.MerchantMaterials,
        )

    # —— Step 6: Legacy scroll selling disabled; Merchant Rules owns sell/keep/salvage logic. ——
    if custom_cleanup_enabled and merchant_xy:
        mx, my = merchant_xy
        ConsoleLog(BOT_NAME, "[Merchant] Dispatching sell_scrolls to alts")
        sell_scroll_refs = _dispatch_to_alts(
            SharedCommandType.MerchantMaterials,
            (mx, my, 0, 0),
            ("sell_scrolls", _SCROLL_MODEL_FILTER, "", ""),
        )
        yield from _coro_sell_scrolls(mx, my)
        yield from _wait_for_alt_dispatch_completion("sell_scrolls", sell_scroll_refs, SharedCommandType.MerchantMaterials)

    # —— Step 7: Restock kits (leader + alts) — after all selling to maximise free space
    if merchant_xy:
        mx, my = merchant_xy
        ConsoleLog(BOT_NAME, f"[Merchant] Merchant at ({mx:.0f}, {my:.0f}) — dispatching kits to alts")
        kit_refs = _dispatch_to_alts(
            SharedCommandType.MerchantItems,
            (mx, my, _merchant_id_kits_target, _merchant_salvage_kits_target),
        )
        yield from bot.Move._coro_xy_and_interact_npc(mx, my, "GH Merchant")
        yield from Routines.Yield.wait(1200)
        id_kits     = _count_model_in_inventory(_ModelID.Identification_Kit.value)
        sup_id_kits = _count_model_in_inventory(_ModelID.Superior_Identification_Kit.value)
        salvage_kits = _count_model_in_inventory(_ModelID.Salvage_Kit.value)
        id_to_buy      = max(0, _merchant_id_kits_target     - (id_kits + sup_id_kits))
        salvage_to_buy = max(0, _merchant_salvage_kits_target - salvage_kits)
        ConsoleLog(BOT_NAME, f"[Merchant] Buying {id_to_buy} ID kits, {salvage_to_buy} salvage kits")
        yield from Routines.Yield.Merchant.BuyIDKits(id_to_buy, log=True)
        yield from Routines.Yield.Merchant.BuySalvageKits(salvage_to_buy, log=True)
        yield from _wait_for_alt_dispatch_completion("restock_kits", kit_refs, SharedCommandType.MerchantItems)
        yield from Routines.Yield.wait(300)
    else:
        ConsoleLog(BOT_NAME, "[Merchant] No Merchant NPC found — skipping kit purchase")

    # —— Step 6: Sell Diamonds & Onyx to Rare Material Trader (leader + alts) ——
    if custom_cleanup_enabled and _merchant_sell_rare_mats:
        if rare_xy:
            rx, ry = rare_xy
            ConsoleLog(BOT_NAME, "[Merchant] Dispatching sell_rare_mats (Diamond/Onyx) to alts")
            rare_sell_refs = _dispatch_to_alts(
                SharedCommandType.MerchantMaterials,
                (rx, ry, 0, 0),
                ("sell_rare_mats", _RARE_MAT_FILTER, "", ""),
            )
            ConsoleLog(BOT_NAME, "[Merchant] Selling Diamond/Onyx at Rare Material Trader (leader)")
            yield from _coro_sell_rare_mats_at_trader(rx, ry, _RARE_MAT_MODELS)
            yield from _wait_for_alt_dispatch_completion(
                "sell_rare_mats",
                rare_sell_refs,
                SharedCommandType.MerchantMaterials,
            )
        else:
            ConsoleLog(BOT_NAME, "[Merchant] No Rare Material Trader found — skipping rare mat sell")

    # —— Step 7: Buy ectos from storage excess (leader + alts independently)
    # Storage is PER-ACCOUNT in GW — each account checks its own storage independently.
    # Always dispatch to alts so each alt can buy if ITS OWN storage exceeds threshold.
    if custom_cleanup_enabled and _merchant_buy_ectos and rare_xy:
        rx, ry = rare_xy
        ConsoleLog(BOT_NAME, f"[Merchant] Dispatching buy_ectoplasm to all alts (threshold={_merchant_ecto_threshold:,})")
        buy_ecto_refs = _dispatch_to_alts(
            SharedCommandType.MerchantMaterials,
            (rx, ry, _merchant_ecto_threshold, _merchant_ecto_threshold),
            ("buy_ectoplasm", "1", "0", ""),  # use_storage_gold=True; each alt checks own storage
        )
        # Leader buys from its own storage independently
        leader_storage = int(GLOBAL_CACHE.Inventory.GetGoldInStorage())
        if leader_storage > _merchant_ecto_threshold:
            ConsoleLog(BOT_NAME, f"[Merchant] Leader buying ectos (storage={leader_storage:,}, threshold={_merchant_ecto_threshold:,})")
            yield from Routines.Yield.Merchant.BuyEctoplasm(
                rx, ry,
                use_storage_gold=True,
                start_threshold=_merchant_ecto_threshold,
                stop_threshold=_merchant_ecto_threshold,
            )
        else:
            ConsoleLog(BOT_NAME, f"[Merchant] Leader storage ({leader_storage:,}) at/below threshold — skipping leader ecto buy")
        yield from _wait_for_alt_dispatch_completion("buy_ectoplasm", buy_ecto_refs, SharedCommandType.MerchantMaterials)
    elif custom_cleanup_enabled and _merchant_buy_ectos:
        ConsoleLog(BOT_NAME, "[Merchant] Ecto buy skipped — no Rare Material Trader found")

    # —— Step 8: Wait for alts to finish their queued actions —————————————————
    if _merchant_alt_wait_ms > 0:
        ConsoleLog(BOT_NAME, f"[Merchant] Final settle wait {_merchant_alt_wait_ms}ms")
        yield from Routines.Yield.wait(_merchant_alt_wait_ms)

    # —— Step 9: Return to Vlox's Fall ————————————————————————————————————————
    ConsoleLog(BOT_NAME, "[Merchant] Returning to Vlox's Fall")
    yield from _coro_travel_random_district(GADDS_ENCAMPMENT)
    ConsoleLog(BOT_NAME, "[Merchant] Guild Hall merchant run complete")
    yield

def _resign_all_to_outpost_before_merchant() -> Generator[Any, Any, bool]:
    ConsoleLog(BOT_NAME, "[Merchant] Resigning all accounts before Guild Hall merchant routine")
    start_map_id = int(Map.GetMapID())
    my_email = Player.GetAccountEmail()
    for acc in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if acc.AccountEmail != my_email:
            GLOBAL_CACHE.ShMem.SendMessage(my_email, acc.AccountEmail, SharedCommandType.Resign, (0, 0, 0, 0), ("", "", "", ""))
    Player.SendChatCommand("resign")
    yield from Routines.Yield.wait(500)

    # Never block the run forever here. If resign does not complete, skip the GH
    # merchant pass and let the normal Sparkfly/Tekks loop continue.
    outpost_deadline = time.time() + 60.0
    while time.time() < outpost_deadline:
        if Map.IsOutpost() and Routines.Checks.Map.MapValid():
            ConsoleLog(BOT_NAME, "[Merchant] Resign complete; outpost loaded.", Py4GW.Console.MessageType.Info)
            return True
        yield from Routines.Yield.wait(250)

    ConsoleLog(
        BOT_NAME,
        f"[Merchant] Resign/outpost wait timed out after 60s (start_map={start_map_id}, current_map={Map.GetMapID()}); skipping GH merchant pass.",
        Py4GW.Console.MessageType.Warning,
    )
    return False


def _summon_and_invite_party(settle_ms: int = 1000) -> Generator:
    """Summon all alts to the leader's current map+district, then invite with retries.

    settle_ms -- extra wait after all alts have arrived before sending invites.
                 Use a larger value (e.g. 2500) after a Guild Hall merchant run
                 to give accounts more time to fully settle.
    """
    _my_email = Player.GetAccountEmail()
    _live_map = int(Map.GetMapID())

    # --- Wait for the leader's own ShMem to reflect the live map ---
    # Required so the district/region/language comparison below is valid.
    _ld_deadline = time.time() + 15.0
    while time.time() < _ld_deadline:
        _ld = GLOBAL_CACHE.ShMem.GetAccountDataFromEmail(_my_email)
        if _ld and int(_ld.AgentData.Map.MapID) == _live_map:
            break
        yield from Routines.Yield.wait(250)
    else:
        ConsoleLog(BOT_NAME, "[Party] Leader ShMem did not update in time — proceeding anyway", Py4GW.Console.MessageType.Warning)

    _ld = GLOBAL_CACHE.ShMem.GetAccountDataFromEmail(_my_email)
    if not _ld:
        ConsoleLog(BOT_NAME, "[Party] Could not read leader ShMem — skipping invite", Py4GW.Console.MessageType.Warning)
        yield
        return

    # --- Snapshot alt count BEFORE dispatching travel commands ---
    # GetAllAccountData() shrinks while alts are mid-travel (they temporarily
    # drop out of ShMem during map transitions). A fixed denominator prevents
    # the arrival check from satisfying itself prematurely.
    _expected_alt_count = len([
        acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData()
        if acc.AccountEmail != _my_email
    ])
    _expected_size = _expected_alt_count + 1  # leader + all alts

    ConsoleLog(BOT_NAME, f"[Party] Summoning {_expected_alt_count} alt(s) to current map")
    yield from bot.Multibox._helpers.Multibox._summon_all_accounts()

    # --- Wait until every alt's ShMem shows the same MapID+Region+Language+District ---
    # All four fields are required: Europe-Spanish-District1 and Europe-German-District1
    # share a MapID but are completely different zone instances.
    _arrival_deadline = time.time() + 90.0
    ConsoleLog(BOT_NAME, f"[Party] Waiting for {_expected_alt_count} alt(s) to arrive on map {_live_map} "
                         f"(region={_ld.AgentData.Map.Region} language={_ld.AgentData.Map.Language} district={_ld.AgentData.Map.District})")
    while time.time() < _arrival_deadline:
        _accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
        _arrived  = sum(
            1 for acc in _accounts
            if (acc.AccountEmail != _my_email                              and
                int(acc.AgentData.Map.MapID) == _live_map                  and
                acc.AgentData.Map.Region     == _ld.AgentData.Map.Region   and
                acc.AgentData.Map.Language   == _ld.AgentData.Map.Language and
                acc.AgentData.Map.District   == _ld.AgentData.Map.District)
        )
        if _arrived >= _expected_alt_count:
            ConsoleLog(BOT_NAME, f"[Party] All {_expected_alt_count} alt(s) on correct district — settling")
            break
        ConsoleLog(BOT_NAME, f"[Party] {_arrived}/{_expected_alt_count} alts on correct district — waiting")
        yield from Routines.Yield.wait(1000)
    else:
        _accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()
        _arrived  = sum(
            1 for acc in _accounts
            if (acc.AccountEmail != _my_email                              and
                int(acc.AgentData.Map.MapID) == _live_map                  and
                acc.AgentData.Map.Region     == _ld.AgentData.Map.Region   and
                acc.AgentData.Map.Language   == _ld.AgentData.Map.Language and
                acc.AgentData.Map.District   == _ld.AgentData.Map.District)
        )
        ConsoleLog(BOT_NAME, f"[Party] Arrival timeout — {_arrived}/{_expected_alt_count} on correct district. Proceeding.", Py4GW.Console.MessageType.Warning)

    yield from Routines.Yield.wait(settle_ms)

    # --- Invite with retries ---
    # The framework method handles per-account matching (MapID+Region+Language+District+PartyID)
    # and profession-priority ordering.
    for _attempt in range(3):
        ConsoleLog(BOT_NAME, f"[Party] Sending invites (attempt {_attempt + 1})")
        yield from bot.Multibox._helpers.Multibox._invite_all_accounts()

        _party_deadline = time.time() + 10.0
        while time.time() < _party_deadline:
            if Party.GetPartySize() >= _expected_size:
                break
            yield from Routines.Yield.wait(500)

        _actual = Party.GetPartySize()
        if _actual >= _expected_size:
            ConsoleLog(BOT_NAME, f"[Party] Party full ({_actual}/{_expected_size}) after attempt {_attempt + 1}", log=True)
            yield
            return

        ConsoleLog(BOT_NAME, f"[Party] Party incomplete ({_actual}/{_expected_size}) — retrying", Py4GW.Console.MessageType.Warning)
        yield from Routines.Yield.wait(1500)

    _actual = Party.GetPartySize()
    ConsoleLog(BOT_NAME, f"[Party] Still incomplete after 3 attempts ({_actual}/{_expected_size}) — proceeding", Py4GW.Console.MessageType.Warning)
    yield

def _gh_merchant_setup_for_alt_salvage_threshold() -> Generator:
    if not _merchant_enabled:
        ConsoleLog(BOT_NAME, "[Merchant] Skipping alt salvage restock check: merchant routine disabled.", Py4GW.Console.MessageType.Info)
        yield
        return

    _write_local_salvage_kit_count()
    yield from _request_alt_salvage_kit_counts()
    needs_restock, low_accounts, unknown_accounts = _alts_need_salvage_restock()
    if unknown_accounts:
        ConsoleLog(
            BOT_NAME,
            f"[Merchant] Alt salvage count unknown this pass: {', '.join(unknown_accounts)}",
            Py4GW.Console.MessageType.Warning,
        )
    if not needs_restock:
        yield
        return

    ConsoleLog(
        BOT_NAME,
        f"[Merchant] Alt salvage trigger hit: {', '.join(low_accounts)}. Running Guild Hall merchant routine.",
    )
    resigned = yield from _resign_all_to_outpost_before_merchant()
    if not resigned:
        yield
        return
    yield from Routines.Yield.wait(3000)
    yield from _gh_merchant_setup(leave_party=True)
    bot.config.FSM.jump_to_state_by_name("Reset Post Merchant")


def _get_shared_memory_free_slot_count(account_email: str) -> int:
    """Best-effort free-slot count from shared-memory inventory bags; avoids requiring an IPC reply."""
    try:
        account = GLOBAL_CACHE.ShMem.GetAccountDataFromEmail(account_email)
        if account is None:
            return -1
        total_size = 0
        occupied = 0
        for bag in account.InventoryBags.iter_bags():
            bag_size = int(getattr(bag, "Size", 0) or 0)
            if bag_size <= 0:
                continue
            total_size += bag_size
            for slot_index in range(min(bag_size, len(bag.Slots))):
                slot = bag.Slots[slot_index]
                model_id = int(getattr(slot, "ModelID", 0) or 0)
                quantity = int(getattr(slot, "Quantity", 0) or 0)
                if model_id > 0 and quantity > 0:
                    occupied += 1
        if total_size <= 0:
            return -1
        return max(0, total_size - occupied)
    except Exception:
        return -1


def _request_alt_free_slot_counts() -> Generator[Any, Any, tuple[list[tuple[str, int]], list[str], list[tuple[str, int]]]]:
    """Return (low_accounts, unknown_accounts, ok_accounts) for alt free slots using the merchant widget threshold."""
    my_email = Player.GetAccountEmail()
    alt_accounts = [acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData() if acc.AccountEmail and acc.AccountEmail != my_email]
    if not alt_accounts:
        return [], [], []

    low_accounts: list[tuple[str, int]] = []
    unknown_accounts: list[str] = []
    ok_accounts: list[tuple[str, int]] = []
    pending: dict[str, str] = {}

    # Dispatch all requests first, then wait once for the whole party.  This avoids
    # looking stuck at this step for N * timeout when several alts are slow/offline.
    for acc in alt_accounts:
        name = acc.AgentData.CharacterName or acc.AccountEmail
        pending[acc.AccountEmail] = name
        reset_inventory_count(acc.AccountEmail, 0, 0)
        GLOBAL_CACHE.ShMem.SendMessage(
            my_email,
            acc.AccountEmail,
            SharedCommandType.InventoryQuery,
            (0.0, 0.0, 0.0, 0.0),
            ("report_free_slots",),
        )

    deadline = time.time() + (_FROGGY_IPC_POLL_MAX_TOTAL_MS / 1000.0)
    while pending and time.time() < deadline:
        for account_email, name in list(pending.items()):
            free_slots = get_inventory_count(account_email, 0, 0)
            if free_slots < 0:
                continue
            pending.pop(account_email, None)
            if free_slots <= _inventory_slots_threshold:
                low_accounts.append((name, free_slots))
            else:
                ok_accounts.append((name, free_slots))
        if pending:
            yield from Routines.Yield.wait(_FROGGY_IPC_POLL_TIMEOUT_MS)

    # If the IPC handler did not answer (e.g. alts have not reloaded Messaging.py),
    # fall back to the inventory snapshot already published in shared memory.
    for account_email, name in list(pending.items()):
        free_slots = _get_shared_memory_free_slot_count(account_email)
        if free_slots < 0:
            unknown_accounts.append(name)
        elif free_slots <= _inventory_slots_threshold:
            low_accounts.append((name, free_slots))
        else:
            ok_accounts.append((name, free_slots))

    return low_accounts, unknown_accounts, ok_accounts


def _gh_merchant_setup_if_inventory_full() -> Generator:
    """After quest reward: if merchant is enabled and any account has low free slots, run GH merchant."""
    if not _merchant_enabled:
        ConsoleLog(BOT_NAME, "[Merchant] Skipping inventory restock check: merchant routine disabled.", Py4GW.Console.MessageType.Info)
        yield
        return

    leader_free_slots = int(GLOBAL_CACHE.Inventory.GetFreeSlotCount())
    ConsoleLog(
        BOT_NAME,
        f"[Merchant] Free-slot threshold check: leader={leader_free_slots}, threshold={_inventory_slots_threshold}.",
        Py4GW.Console.MessageType.Info,
    )

    low_accounts: list[tuple[str, int]] = []
    ok_accounts: list[tuple[str, int]] = []
    if leader_free_slots <= _inventory_slots_threshold:
        low_accounts.append((Player.GetName() or "Leader", leader_free_slots))
    else:
        ok_accounts.append((Player.GetName() or "Leader", leader_free_slots))

    alt_low_accounts, unknown_accounts, alt_ok_accounts = yield from _request_alt_free_slot_counts()
    low_accounts.extend(alt_low_accounts)
    ok_accounts.extend(alt_ok_accounts)

    if unknown_accounts:
        ConsoleLog(
            BOT_NAME,
            f"[Merchant] Alt free-slot count unknown this pass: {', '.join(unknown_accounts)}",
            Py4GW.Console.MessageType.Warning,
        )

    if not low_accounts:
        ok_summary = ", ".join(f"{name}={slots}" for name, slots in ok_accounts) or "none"
        ConsoleLog(
            BOT_NAME,
            f"[Merchant] Inventory free slots OK on all known accounts (threshold={_inventory_slots_threshold}; {ok_summary}).",
            Py4GW.Console.MessageType.Info,
        )
        yield
        return

    low_summary = ", ".join(f"{name}={slots}" for name, slots in low_accounts)
    ConsoleLog(
        BOT_NAME,
        f"[Merchant] Inventory threshold hit ({low_summary}; threshold={_inventory_slots_threshold}) — resigning to outpost then triggering GH merchant run",
    )

    resigned = yield from _resign_all_to_outpost_before_merchant()
    if not resigned:
        yield
        return
    yield from Routines.Yield.wait(3000)
    yield from _gh_merchant_setup(leave_party=True)
    bot.config.FSM.jump_to_state_by_name("Reset Post Merchant")

# --- Config Load / Save ---

def _ensure_ini_initialized() -> bool:
    """Load all settings and statistics from INI on first call. Returns True when ready."""
    global _settings_loaded
    global _use_hard_mode, _randomize_district, _use_precons_running, _use_precons_level1, _use_precons_level2
    global _merchant_enabled, _merchant_id_kits_target, _merchant_salvage_kits_target
    global _inventory_slots_threshold, _merchant_store_consumable_materials
    global _merchant_sell_materials, _merchant_sell_rare_mats, _merchant_buy_ectos
    global _merchant_ecto_threshold, _merchant_alt_wait_ms
    global _total_runs, _total_run_time, _fastest_run, _slowest_run
    global _l1_total_time, _l1_fastest, _l1_slowest
    global _l2_total_time, _l2_fastest, _l2_slowest
    global _froggy_drops, _gb_drops

    if _settings_loaded:
        return True

    _S = _SETTINGS_SECTION
    _use_hard_mode      = _settings_ini.read_bool(_S, "use_hard_mode",      True)
    _randomize_district = _settings_ini.read_bool(_S, "randomize_district", True)
    _legacy_precons     = _settings_ini.read_bool(_S, "use_precons",        True)
    _use_precons_running = _settings_ini.read_bool(_S, "use_precons_running", _legacy_precons)
    _use_precons_level1  = _settings_ini.read_bool(_S, "use_precons_level1",  _legacy_precons)
    _use_precons_level2  = _settings_ini.read_bool(_S, "use_precons_level2",  _legacy_precons)

    _M = _MERCHANT_SECTION
    _merchant_enabled                    = _settings_ini.read_bool(_M, "enabled",                    False)
    _merchant_id_kits_target             = _settings_ini.read_int( _M, "id_kits_target",             _FIXED_ID_KITS_TARGET)
    _merchant_salvage_kits_target        = _settings_ini.read_int( _M, "salvage_kits_target",        _FIXED_SALVAGE_KITS_TARGET)
    _inventory_slots_threshold           = max(0, _settings_ini.read_int(_M, "inventory_threshold",  1))
    _merchant_store_consumable_materials = _settings_ini.read_bool(_M, "store_consumable_materials", False)
    _merchant_sell_materials             = _settings_ini.read_bool(_M, "sell_materials",             False)
    _merchant_sell_rare_mats             = _settings_ini.read_bool(_M, "sell_rare_mats",             False)
    _merchant_buy_ectos                  = _settings_ini.read_bool(_M, "buy_ectos",                  False)
    _merchant_ecto_threshold             = _settings_ini.read_int( _M, "ecto_threshold",             800_000)
    _merchant_alt_wait_ms                = max(0, min(_MAX_ALT_SETTLE_WAIT_MS, _settings_ini.read_int(_M, "alt_wait_ms", _DEFAULT_ALT_SETTLE_WAIT_MS)))

    _SS = _STATS_SECTION
    _total_runs      = _settings_ini.read_int(  _SS, "total_runs",     0)
    _total_run_time  = _settings_ini.read_float(_SS, "total_run_time", 0.0)
    _f  = _settings_ini.read_float(_SS, "fastest_run", 0.0)
    _fastest_run     = float('inf') if _f  == 0.0 else _f
    _slowest_run     = _settings_ini.read_float(_SS, "slowest_run",    0.0)
    _l1_total_time   = _settings_ini.read_float(_SS, "l1_total_time",  0.0)
    _f1 = _settings_ini.read_float(_SS, "l1_fastest", 0.0)
    _l1_fastest      = float('inf') if _f1 == 0.0 else _f1
    _l1_slowest      = _settings_ini.read_float(_SS, "l1_slowest",     0.0)
    _l2_total_time   = _settings_ini.read_float(_SS, "l2_total_time",  0.0)
    _f2 = _settings_ini.read_float(_SS, "l2_fastest", 0.0)
    _l2_fastest      = float('inf') if _f2 == 0.0 else _f2
    _l2_slowest      = _settings_ini.read_float(_SS, "l2_slowest",     0.0)

    # Load all-time FROGGY drop totals so the UI shows correct values from the start
    # and _accumulate_froggy adds on top of the correct base rather than starting from 0.
    _D = _FROGGY_DROPS_SECTION
    for _drop_key in _settings_ini.list_keys(_D):
        _froggy_drops[_drop_key] = _settings_ini.read_int(_D, _drop_key, 0)

    # Seed any accounts seen in other sections that don't have a [FROGGY Drops] entry yet.
    # This ensures the UI shows all known accounts with 0 even before their first drop.
    for _seed_section in (_ALT_SALVAGE_SECTION, _FROGGY_SNAPSHOT_SECTION, _FROGGY_RUN_SECTION):
        for _seed_key in _settings_ini.list_keys(_seed_section):
            if _seed_key not in _froggy_drops:
                _froggy_drops[_seed_key] = 0

    _GD = _GB_DROPS_SECTION
    for _drop_key in _settings_ini.list_keys(_GD):
        _gb_drops[_drop_key] = _settings_ini.read_int(_GD, _drop_key, 0)
    for _seed_section in (_ALT_SALVAGE_SECTION, _GB_SNAPSHOT_SECTION, _GB_RUN_SECTION):
        for _seed_key in _settings_ini.list_keys(_seed_section):
            if _seed_key not in _gb_drops:
                _gb_drops[_seed_key] = 0

    _CN = _CHAR_NAMES_SECTION
    for _cn_key in _settings_ini.list_keys(_CN):
        _name = str(_settings_ini.read_key(_CN, _cn_key, "") or "").strip()
        if _name:
            _char_names[_cn_key] = _name

    _settings_loaded = True
    return True


def _write_settings() -> None:
    """Write all settings, statistics, and FROGGY drop totals to INI if a save has been requested."""
    global _save_requested
    if not _save_requested:
        return

    _S = _SETTINGS_SECTION
    _settings_ini.write_key(_S, "use_hard_mode",      str(_use_hard_mode))
    _settings_ini.write_key(_S, "randomize_district", str(_randomize_district))
    _settings_ini.write_key(_S, "use_precons_running", str(_use_precons_running))
    _settings_ini.write_key(_S, "use_precons_level1",  str(_use_precons_level1))
    _settings_ini.write_key(_S, "use_precons_level2",  str(_use_precons_level2))

    _M = _MERCHANT_SECTION
    _settings_ini.write_key(_M, "enabled",                    str(_merchant_enabled))
    _settings_ini.write_key(_M, "id_kits_target",             str(_merchant_id_kits_target))
    _settings_ini.write_key(_M, "salvage_kits_target",        str(_merchant_salvage_kits_target))
    _settings_ini.write_key(_M, "inventory_threshold",        str(_inventory_slots_threshold))
    _settings_ini.write_key(_M, "store_consumable_materials", str(_merchant_store_consumable_materials))
    _settings_ini.write_key(_M, "sell_materials",             str(_merchant_sell_materials))
    _settings_ini.write_key(_M, "sell_rare_mats",             str(_merchant_sell_rare_mats))
    _settings_ini.write_key(_M, "buy_ectos",                  str(_merchant_buy_ectos))
    _settings_ini.write_key(_M, "ecto_threshold",             str(_merchant_ecto_threshold))
    _settings_ini.write_key(_M, "alt_wait_ms",                str(_merchant_alt_wait_ms))

    _SS = _STATS_SECTION
    _settings_ini.write_key(_SS, "total_runs",     str(_total_runs))
    _settings_ini.write_key(_SS, "total_run_time", str(_total_run_time))
    _f  = 0.0 if _fastest_run == float('inf') else _fastest_run
    _settings_ini.write_key(_SS, "fastest_run",    str(_f))
    _settings_ini.write_key(_SS, "slowest_run",    str(_slowest_run))
    _f1 = 0.0 if _l1_fastest == float('inf') else _l1_fastest
    _settings_ini.write_key(_SS, "l1_total_time",  str(_l1_total_time))
    _settings_ini.write_key(_SS, "l1_fastest",     str(_f1))
    _settings_ini.write_key(_SS, "l1_slowest",     str(_l1_slowest))
    _f2 = 0.0 if _l2_fastest == float('inf') else _l2_fastest
    _settings_ini.write_key(_SS, "l2_total_time",  str(_l2_total_time))
    _settings_ini.write_key(_SS, "l2_fastest",     str(_f2))
    _settings_ini.write_key(_SS, "l2_slowest",     str(_l2_slowest))


    _D = _FROGGY_DROPS_SECTION
    for key, total in _froggy_drops.items():
        _settings_ini.write_key(_D, key, str(total))

    _GD = _GB_DROPS_SECTION
    for key, total in _gb_drops.items():
        _settings_ini.write_key(_GD, key, str(total))

    _CN = _CHAR_NAMES_SECTION
    for key, name in _char_names.items():
        _settings_ini.write_key(_CN, key, name)

    _save_requested = False


def _save_settings() -> None:
    global _save_requested
    _save_requested = True


# --- Run Timing ---

def _mark_run_start() -> Generator:
    global _t_run_start, _t_l2_start, _current_l1_time, _current_l2_time
    _t_run_start     = time.time()
    _t_l2_start      = 0.0
    _current_l1_time = 0.0
    _current_l2_time = 0.0
    yield


def _mark_l2_start() -> Generator:
    global _t_l2_start, _current_l1_time
    _t_l2_start     = time.time()
    _current_l1_time = _t_l2_start - _t_run_start if _t_run_start > 0 else 0.0
    yield



def _record_run_end() -> Generator:
    """Record per-floor and overall run timings, increment run counter, persist."""
    global _total_runs, _session_runs
    global _total_run_time, _fastest_run, _slowest_run
    global _l1_total_time, _l1_fastest, _l1_slowest
    global _l2_total_time, _l2_fastest, _l2_slowest
    global _current_run_time, _current_l2_time

    now = time.time()
    if _t_run_start > 0 and _t_l2_start > 0:
        run_time = now - _t_run_start
        l1_time  = _t_l2_start - _t_run_start
        l2_time  = now - _t_l2_start

        _current_run_time = run_time
        _current_l2_time  = l2_time

        _total_run_time += run_time
        if run_time < _fastest_run: _fastest_run = run_time
        if run_time > _slowest_run: _slowest_run = run_time

        _l1_total_time += l1_time
        if l1_time < _l1_fastest: _l1_fastest = l1_time
        if l1_time > _l1_slowest: _l1_slowest = l1_time

        _l2_total_time += l2_time
        if l2_time < _l2_fastest: _l2_fastest = l2_time
        if l2_time > _l2_slowest: _l2_slowest = l2_time


        ConsoleLog(BOT_NAME, f"[Run Timing] Total: {run_time:.0f}s  L1: {l1_time:.0f}s  L2: {l2_time:.0f}s")

    _total_runs   += 1
    _session_runs += 1
    _save_settings()
    yield


# --- FROGGY Drop Tracking ---

def _take_dungeon_entry_snapshot() -> Generator:
    """Take dungeon-entry snapshot of FROGGY and GB counts: leader counts own inventory, alts report via IPC.

    Alts are queried ONE AT A TIME so each alt has exclusive access to the INI file
    before the next write goes out.  IniHandler does a full read-modify-write of the
    entire file on every write_key() call; if two alts write concurrently the last
    writer silently overwrites the other's result, leaving that account at the -1
    sentinel and causing its drop to be lost.
    """
    global _froggy_pre_snapshot, _gb_pre_snapshot
    my_email     = Player.GetAccountEmail()
    alt_accounts = [acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData() if acc.AccountEmail != my_email]

    # Leader: take own in-memory snapshot and also write it to the INI so the
    # leader's key appears in [FROGGY Snapshot] / [FROGGY Run] the same as alts.
    _froggy_pre_snapshot = {}
    for model_id in FROGGY_MODEL_IDS:
        count = int(GLOBAL_CACHE.Inventory.GetModelCount(model_id))
        if count > 0:
            _froggy_pre_snapshot[model_id] = count
    leader_snap_total = sum(_froggy_pre_snapshot.values())
    _settings_ini.write_key(_FROGGY_SNAPSHOT_SECTION, _account_key(my_email), str(leader_snap_total))
    ConsoleLog(BOT_NAME, f"[FROGGY Stats] Leader dungeon-entry snapshot: {leader_snap_total} FROGGY")

    _gb_pre_snapshot = int(GLOBAL_CACHE.Inventory.GetModelCount(GB_MODEL_ID))
    _settings_ini.write_key(_GB_SNAPSHOT_SECTION, _account_key(my_email), str(_gb_pre_snapshot))
    ConsoleLog(BOT_NAME, f"[FROGGY Stats] Leader dungeon-entry GB snapshot: {_gb_pre_snapshot}")

    if not alt_accounts:
        yield
        return

    max_attempts = max(1, _FROGGY_IPC_POLL_MAX_TOTAL_MS // max(1, _FROGGY_IPC_POLL_TIMEOUT_MS))

    # Sequential querying is optional now -- host is sole INI writer.
    for acc in alt_accounts:
        acc_key = _account_key(acc.AccountEmail)

        reset_inventory_count(acc.AccountEmail, FROGGY_MODEL_ID_MIN, FROGGY_MODEL_ID_MAX)
        _settings_ini.write_key(_FROGGY_SNAPSHOT_SECTION, acc_key, str(-1))
        GLOBAL_CACHE.ShMem.SendMessage(
            my_email, acc.AccountEmail,
            SharedCommandType.InventoryQuery,
            (float(FROGGY_MODEL_ID_MIN), float(FROGGY_MODEL_ID_MAX), 0.0, 0.0),
            ("report_inventory_count",),
        )
        responded = False
        for _ in range(max_attempts):
            yield from Routines.Yield.wait(_FROGGY_IPC_POLL_TIMEOUT_MS)
            count = get_inventory_count(acc.AccountEmail, FROGGY_MODEL_ID_MIN, FROGGY_MODEL_ID_MAX)
            if count >= 0:
                _settings_ini.write_key(_FROGGY_SNAPSHOT_SECTION, acc_key, str(count))
                responded = True
                break
        if not responded:
            name = acc.AgentData.CharacterName or acc.AccountEmail
            ConsoleLog(BOT_NAME, f"[FROGGY Stats] FROGGY snapshot timeout for: {name}", Py4GW.Console.MessageType.Warning)

        reset_inventory_count(acc.AccountEmail, GB_MODEL_ID, GB_MODEL_ID)
        _settings_ini.write_key(_GB_SNAPSHOT_SECTION, acc_key, str(-1))
        GLOBAL_CACHE.ShMem.SendMessage(
            my_email, acc.AccountEmail,
            SharedCommandType.InventoryQuery,
            (float(GB_MODEL_ID), float(GB_MODEL_ID), 0.0, 0.0),
            ("report_inventory_count",),
        )
        responded = False
        for _ in range(max_attempts):
            yield from Routines.Yield.wait(_FROGGY_IPC_POLL_TIMEOUT_MS)
            count = get_inventory_count(acc.AccountEmail, GB_MODEL_ID, GB_MODEL_ID)
            if count >= 0:
                _settings_ini.write_key(_GB_SNAPSHOT_SECTION, acc_key, str(count))
                responded = True
                break
        if not responded:
            name = acc.AgentData.CharacterName or acc.AccountEmail
            ConsoleLog(BOT_NAME, f"[FROGGY Stats] GB snapshot timeout for: {name}", Py4GW.Console.MessageType.Warning)

    yield


def _record_drops_after_loot() -> Generator:
    """Request post-chest FROGGY and GB counts from alts, compute deltas, accumulate totals."""
    my_email     = Player.GetAccountEmail()
    my_key       = _account_key(my_email)
    alt_accounts = [acc for acc in GLOBAL_CACHE.ShMem.GetAllAccountData() if acc.AccountEmail != my_email]

    # Leader: compute own post-chest total and write it to [FROGGY Run] / [GB Run].
    leader_post_total = sum(int(GLOBAL_CACHE.Inventory.GetModelCount(m)) for m in FROGGY_MODEL_IDS)
    _settings_ini.write_key(_FROGGY_RUN_SECTION, my_key, str(leader_post_total))
    ConsoleLog(BOT_NAME, f"[FROGGY Stats] Leader post-chest total: {leader_post_total} FROGGY", log=True)

    leader_gb_post = int(GLOBAL_CACHE.Inventory.GetModelCount(GB_MODEL_ID))
    _settings_ini.write_key(_GB_RUN_SECTION, my_key, str(leader_gb_post))
    ConsoleLog(BOT_NAME, f"[FROGGY Stats] Leader post-chest GB total: {leader_gb_post}", log=True)

    if alt_accounts:
        max_attempts = max(1, _FROGGY_IPC_POLL_MAX_TOTAL_MS // max(1, _FROGGY_IPC_POLL_TIMEOUT_MS))

        # Sequential querying is optional now -- host is sole INI writer.
        for acc in alt_accounts:
            acc_key = _account_key(acc.AccountEmail)

            reset_inventory_count(acc.AccountEmail, FROGGY_MODEL_ID_MIN, FROGGY_MODEL_ID_MAX)
            _settings_ini.write_key(_FROGGY_RUN_SECTION, acc_key, str(-1))
            GLOBAL_CACHE.ShMem.SendMessage(
                my_email, acc.AccountEmail,
                SharedCommandType.InventoryQuery,
                (float(FROGGY_MODEL_ID_MIN), float(FROGGY_MODEL_ID_MAX), 0.0, 0.0),
                ("report_inventory_count",),
            )
            responded = False
            for _ in range(max_attempts):
                yield from Routines.Yield.wait(_FROGGY_IPC_POLL_TIMEOUT_MS)
                count = get_inventory_count(acc.AccountEmail, FROGGY_MODEL_ID_MIN, FROGGY_MODEL_ID_MAX)
                if count >= 0:
                    _settings_ini.write_key(_FROGGY_RUN_SECTION, acc_key, str(count))
                    responded = True
                    break
            if not responded:
                name = acc.AgentData.CharacterName or acc.AccountEmail
                ConsoleLog(BOT_NAME, f"[FROGGY Stats] FROGGY count timeout for: {name}", Py4GW.Console.MessageType.Warning)

            reset_inventory_count(acc.AccountEmail, GB_MODEL_ID, GB_MODEL_ID)
            _settings_ini.write_key(_GB_RUN_SECTION, acc_key, str(-1))
            GLOBAL_CACHE.ShMem.SendMessage(
                my_email, acc.AccountEmail,
                SharedCommandType.InventoryQuery,
                (float(GB_MODEL_ID), float(GB_MODEL_ID), 0.0, 0.0),
                ("report_inventory_count",),
            )
            responded = False
            for _ in range(max_attempts):
                yield from Routines.Yield.wait(_FROGGY_IPC_POLL_TIMEOUT_MS)
                count = get_inventory_count(acc.AccountEmail, GB_MODEL_ID, GB_MODEL_ID)
                if count >= 0:
                    _settings_ini.write_key(_GB_RUN_SECTION, acc_key, str(count))
                    responded = True
                    break
            if not responded:
                name = acc.AgentData.CharacterName or acc.AccountEmail
                ConsoleLog(BOT_NAME, f"[FROGGY Stats] GB count timeout for: {name}", Py4GW.Console.MessageType.Warning)

    # Accumulate deltas for ALL accounts (leader + alts) from the INI uniformly.
    all_accounts_keys = [my_key] + [_account_key(acc.AccountEmail) for acc in alt_accounts]
    total_froggy_this_run = 0
    total_gb_this_run  = 0
    for acc_key in all_accounts_keys:
        post_count = _settings_ini.read_int(_FROGGY_RUN_SECTION,      acc_key, -1)
        snap_count = _settings_ini.read_int(_FROGGY_SNAPSHOT_SECTION, acc_key, -1)
        if post_count < 0 or snap_count < 0:
            ConsoleLog(
                BOT_NAME,
                f"[FROGGY Stats] {acc_key}: skipping FROGGY delta because count is unknown (snap={snap_count}, post={post_count}).",
                Py4GW.Console.MessageType.Warning,
            )
        else:
            delta = max(0, post_count - snap_count)
            ConsoleLog(BOT_NAME, f"[FROGGY Stats] {acc_key}: snap={snap_count} post={post_count} delta={delta}", log=True)
            _accumulate_froggy(acc_key, delta)
            total_froggy_this_run += delta

        gb_post = _settings_ini.read_int(_GB_RUN_SECTION,      acc_key, -1)
        gb_snap = _settings_ini.read_int(_GB_SNAPSHOT_SECTION, acc_key, -1)
        if gb_post < 0 or gb_snap < 0:
            ConsoleLog(
                BOT_NAME,
                f"[FROGGY Stats] {acc_key} GB: skipping delta because count is unknown (snap={gb_snap}, post={gb_post}).",
                Py4GW.Console.MessageType.Warning,
            )
        else:
            gb_delta = max(0, gb_post - gb_snap)
            ConsoleLog(BOT_NAME, f"[FROGGY Stats] {acc_key} GB: snap={gb_snap} post={gb_post} delta={gb_delta}", log=True)
            _accumulate_gb(acc_key, gb_delta)
            total_gb_this_run += gb_delta

    ConsoleLog(BOT_NAME, f"[FROGGY Stats] Run complete. FROGGY={total_froggy_this_run} GB={total_gb_this_run}", log=True)
    _save_settings()
    yield


def _accumulate_froggy(account_key: str, run_count: int) -> None:
    """Add run_count to both session and all-time totals for account_key."""
    global _froggy_drops, _session_froggy
    if run_count <= 0:
        return
    current_total = _froggy_drops.get(account_key)
    if current_total is None:
        current_total = _settings_ini.read_int(_FROGGY_DROPS_SECTION, account_key, 0)
    _froggy_drops[account_key]   = current_total + run_count
    _session_froggy[account_key] = _session_froggy.get(account_key, 0) + run_count


def _accumulate_gb(account_key: str, run_count: int) -> None:
    """Add run_count to both session and all-time GB totals for account_key."""
    global _gb_drops, _session_gb
    if run_count <= 0:
        return
    current_total = _gb_drops.get(account_key)
    if current_total is None:
        current_total = _settings_ini.read_int(_GB_DROPS_SECTION, account_key, 0)
    _gb_drops[account_key]   = current_total + run_count
    _session_gb[account_key] = _session_gb.get(account_key, 0) + run_count


# --- Statistics and Run Tracking ---

def _draw_froggy_stats() -> None:
    import PyImGui
    from Py4GWCoreLib import ImGui, Color

    _ensure_ini_initialized()

    # Refresh character name cache from live shared memory (mirrors Isolation Manager pattern)
    _new_names_found = False
    # Include the local account itself (not returned by GetAllAccountData)
    _my_em = str(Player.GetAccountEmail() or "").strip()
    _my_cn = str(Player.GetName() or "").strip()
    if _my_em and _my_cn:
        _my_key = _account_key(_my_em)
        if _char_names.get(_my_key) != _my_cn:
            _char_names[_my_key] = _my_cn
            _new_names_found = True
    for _acc in (GLOBAL_CACHE.ShMem.GetAllAccountData(sort_results=False, include_isolated=True) or []):
        _em  = str(_acc.AccountEmail or "").strip()
        _cn  = str(_acc.AgentData.CharacterName or "").strip()
        if _em and _cn:
            _acc_key = _account_key(_em)
            if _char_names.get(_acc_key) != _cn:
                _char_names[_acc_key] = _cn
                _new_names_found = True
    if _new_names_found:
        _save_settings()

    gold = Color(255, 210,  80, 255).to_tuple_normalized()
    cyan = Color( 80, 210, 255, 255).to_tuple_normalized()
    live = Color(100, 180, 255, 255).to_tuple_normalized()

    def _fmt_time(seconds: float) -> str:
        if seconds <= 0.0 or seconds == float('inf'):
            return "--:--"
        m, s = divmod(int(seconds), 60)
        return f"{m:02d}:{s:02d}"

    def _avg_time(total: float, runs: int) -> str:
        return _fmt_time(total / runs) if runs > 0 else "--:--"

    def _runs_per_drop(runs: int, drops: int) -> str:
        return f"{runs / drops:.1f}" if drops > 0 else "-"

    tbl_flags = (
        PyImGui.TableFlags.Borders        |
        PyImGui.TableFlags.RowBg          |
        PyImGui.TableFlags.SizingFixedFit |
        PyImGui.TableFlags.NoHostExtendX
    )
    _COL_W = 60.0  # standard column width — header text is always the widest element
    _ROW_H = 22    # uniform row height for vertical-centering helpers
    _HDR_COLOR = 26 | (38 << 8) | (51 << 16) | (255 << 24)

    def _vcenter() -> None:
        th = PyImGui.get_text_line_height()
        PyImGui.set_cursor_pos_y(PyImGui.get_cursor_pos_y() + max(0.0, (_ROW_H - th) / 2))

    def _ltext(s: str) -> None:
        _vcenter()
        PyImGui.text(s)

    def _ctext(s: str) -> None:
        _vcenter()
        avail = PyImGui.get_content_region_avail()[0]
        tw    = PyImGui.calc_text_size(s)[0]
        PyImGui.set_cursor_pos_x(PyImGui.get_cursor_pos_x() + max(0.0, (avail - tw) / 2))
        PyImGui.text(s)


    def _rtext(s: str) -> None:
        _vcenter()
        avail = PyImGui.get_content_region_avail()[0]
        tw    = PyImGui.calc_text_size(s)[0]
        PyImGui.set_cursor_pos_x(PyImGui.get_cursor_pos_x() + max(0.0, avail - tw))
        PyImGui.text(s)

    def _rtext_colored(s: str, color) -> None:
        _vcenter()
        avail = PyImGui.get_content_region_avail()[0]
        tw    = PyImGui.calc_text_size(s)[0]
        PyImGui.set_cursor_pos_x(PyImGui.get_cursor_pos_x() + max(0.0, avail - tw))
        PyImGui.text_colored(s, color)

    # ── Header ────────────────────────────────────────────────
    _froggy_icon_exists = os.path.isfile(_FROGGY_ICON_PATH)
    if _froggy_icon_exists:
        ImGui.image(_FROGGY_ICON_PATH, (24, 24))
        PyImGui.same_line(0, 8)
    PyImGui.text_colored("Froggy Statistics", gold)
    PyImGui.separator()
    PyImGui.spacing()

    global _scramble_accounts
    _scramble_accounts = PyImGui.checkbox("Hide Account Names", _scramble_accounts)

    # ── Table 1: Overview ─────────────────────────────────────
    alltime_total_froggy = sum(_froggy_drops.values())
    session_total_froggy = sum(_session_froggy.values())

    layout_flags = PyImGui.TableFlags.NoBordersInBody | PyImGui.TableFlags.SizingStretchProp
    if PyImGui.begin_table("##froggy_overview_layout", 2, layout_flags):
        PyImGui.table_setup_column("##col_session", PyImGui.TableColumnFlags.WidthStretch, 2.0)
        PyImGui.table_setup_column("##col_alltime", PyImGui.TableColumnFlags.WidthStretch, 3.0)

        PyImGui.table_next_row()
        PyImGui.table_set_column_index(0); PyImGui.text_colored("Session Overview", cyan)
        PyImGui.table_set_column_index(1); PyImGui.text_colored("Total Overview", cyan)

        PyImGui.table_next_row()

        PyImGui.table_set_column_index(0)
        if PyImGui.begin_table("##froggy_session", 2, tbl_flags):
            PyImGui.table_setup_column("Runs", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
            PyImGui.table_setup_column("Froggy",  PyImGui.TableColumnFlags.WidthFixed, _COL_W)
            PyImGui.table_next_row(0, _ROW_H); PyImGui.table_set_bg_color(2, _HDR_COLOR, -1)
            PyImGui.table_set_column_index(0); _ctext("Runs")
            PyImGui.table_set_column_index(1); _ctext("Froggy")
            PyImGui.table_next_row(0, _ROW_H)
            PyImGui.table_set_column_index(0); _rtext(str(_session_runs))
            PyImGui.table_set_column_index(1); _rtext(str(session_total_froggy))
            PyImGui.end_table()

        PyImGui.table_set_column_index(1)
        if PyImGui.begin_table("##froggy_alltime", 3, tbl_flags):
            PyImGui.table_setup_column("Runs", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
            PyImGui.table_setup_column("Froggy",  PyImGui.TableColumnFlags.WidthFixed, _COL_W)
            PyImGui.table_setup_column("Avg", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
            PyImGui.table_next_row(0, _ROW_H); PyImGui.table_set_bg_color(2, _HDR_COLOR, -1)
            PyImGui.table_set_column_index(0); _ctext("Runs")
            PyImGui.table_set_column_index(1); _ctext("Froggy")
            PyImGui.table_set_column_index(2); _ctext("Avg")
            PyImGui.table_next_row(0, _ROW_H)
            PyImGui.table_set_column_index(0); _rtext(str(_total_runs))
            PyImGui.table_set_column_index(1); _rtext(str(alltime_total_froggy))
            PyImGui.table_set_column_index(2); _rtext(_runs_per_drop(_total_runs, alltime_total_froggy))
            PyImGui.end_table()

        PyImGui.end_table()

    PyImGui.spacing()

    # ── Table 2: Run Timings ───────────────────────────────────
    PyImGui.text_colored("Run Timings", cyan)
    if PyImGui.begin_table("##froggy_timings", 5, tbl_flags):
        PyImGui.table_setup_column("Floor",   PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Current", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Avg",     PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Best",    PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Worst",   PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_next_row(0, _ROW_H); PyImGui.table_set_bg_color(2, _HDR_COLOR, -1)
        PyImGui.table_set_column_index(0); _ctext("Floor")
        PyImGui.table_set_column_index(1); _ctext("Current")
        PyImGui.table_set_column_index(2); _ctext("Avg")
        PyImGui.table_set_column_index(3); _ctext("Best")
        PyImGui.table_set_column_index(4); _ctext("Worst")

        # Live clocks: tick while the floor/run is in progress, show last completed otherwise
        _now        = time.time()
        _run_active = _t_run_start > 0
        _l1_active  = _run_active and _t_l2_start == 0
        _l2_active  = _t_l2_start > 0
        _live_run   = (_now - _t_run_start) if _run_active else _current_run_time
        _live_l1    = (_now - _t_run_start) if _l1_active  else _current_l1_time
        _live_l2    = (_now - _t_l2_start)  if _l2_active  else _current_l2_time

        timing_rows = [
            ("Overall", _live_run, _run_active, _total_run_time, _fastest_run, _slowest_run),
            ("Floor 1", _live_l1,  _l1_active,  _l1_total_time,  _l1_fastest,  _l1_slowest),
            ("Floor 2", _live_l2,  _l2_active,  _l2_total_time,  _l2_fastest,  _l2_slowest),
        ]
        for label, current, is_live, total, fastest, slowest in timing_rows:
            PyImGui.table_next_row(0, _ROW_H)
            PyImGui.table_set_column_index(0); _ltext(label)
            if is_live:
                PyImGui.table_set_column_index(1); _rtext_colored(_fmt_time(current), live)
            else:
                PyImGui.table_set_column_index(1); _rtext(_fmt_time(current))
            PyImGui.table_set_column_index(2); _rtext(_avg_time(total, _total_runs))
            PyImGui.table_set_column_index(3); _rtext(_fmt_time(fastest))
            PyImGui.table_set_column_index(4); _rtext(_fmt_time(slowest))

        PyImGui.end_table()

    PyImGui.spacing()

    # ── Table 3: FROGGY Drops per account ────────────────────────
    PyImGui.text_colored("Froggy Drops", cyan)
    if PyImGui.begin_table("##froggy_drops", 4, tbl_flags):
        PyImGui.table_setup_column("Account",   PyImGui.TableColumnFlags.WidthStretch)
        PyImGui.table_setup_column("Session",   PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("All Time",  PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Runs/Drop", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_next_row(0, _ROW_H); PyImGui.table_set_bg_color(2, _HDR_COLOR, -1)
        PyImGui.table_set_column_index(0); _ltext("Account")
        PyImGui.table_set_column_index(1); _ctext("Session")
        PyImGui.table_set_column_index(2); _ctext("All Time")
        PyImGui.table_set_column_index(3); _ctext("Avg")

        all_accounts = sorted(set(list(_froggy_drops.keys()) + list(_session_froggy.keys())))
        session_total      = 0
        alltime_acct_total = 0
        for acct in all_accounts:
            s_count = _session_froggy.get(acct, 0)
            a_count = _froggy_drops.get(acct, 0)
            session_total      += s_count
            alltime_acct_total += a_count
            PyImGui.table_next_row(0, _ROW_H)
            PyImGui.table_set_column_index(0); _ltext(_masked_email(acct))
            PyImGui.table_set_column_index(1); _rtext(str(s_count))
            PyImGui.table_set_column_index(2); _rtext(str(a_count))
            PyImGui.table_set_column_index(3); _rtext(_runs_per_drop(_total_runs, a_count))

        # ── Totals footer ──
        PyImGui.table_next_row(0, _ROW_H)
        PyImGui.table_set_column_index(0); _ltext("Total")
        PyImGui.table_set_column_index(1); _rtext_colored(str(session_total), gold)
        PyImGui.table_set_column_index(2); _rtext_colored(str(alltime_acct_total), gold)
        PyImGui.table_set_column_index(3); _rtext_colored(_runs_per_drop(_total_runs, alltime_acct_total), gold)

        PyImGui.end_table()

    PyImGui.spacing()

    # ── Table 4: Glacial Blades Drops per account ──────────────
    PyImGui.text_colored("Glacial Blades Drops", cyan)
    if PyImGui.begin_table("##gb_drops", 4, tbl_flags):
        PyImGui.table_setup_column("Account",   PyImGui.TableColumnFlags.WidthStretch)
        PyImGui.table_setup_column("Session",   PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("All Time",  PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_setup_column("Runs/Drop", PyImGui.TableColumnFlags.WidthFixed, _COL_W)
        PyImGui.table_next_row(0, _ROW_H); PyImGui.table_set_bg_color(2, _HDR_COLOR, -1)
        PyImGui.table_set_column_index(0); _ltext("Account")
        PyImGui.table_set_column_index(1); _ctext("Session")
        PyImGui.table_set_column_index(2); _ctext("All Time")
        PyImGui.table_set_column_index(3); _ctext("Avg")

        all_accounts = sorted(set(list(_gb_drops.keys()) + list(_session_gb.keys())))
        session_total      = 0
        alltime_acct_total = 0
        for acct in all_accounts:
            s_count = _session_gb.get(acct, 0)
            a_count = _gb_drops.get(acct, 0)
            session_total      += s_count
            alltime_acct_total += a_count
            PyImGui.table_next_row(0, _ROW_H)
            PyImGui.table_set_column_index(0); _ltext(_masked_email(acct))
            PyImGui.table_set_column_index(1); _rtext(str(s_count))
            PyImGui.table_set_column_index(2); _rtext(str(a_count))
            PyImGui.table_set_column_index(3); _rtext(_runs_per_drop(_total_runs, a_count))

        # ── Totals footer ──
        PyImGui.table_next_row(0, _ROW_H)
        PyImGui.table_set_column_index(0); _ltext("Total")
        PyImGui.table_set_column_index(1); _rtext_colored(str(session_total), gold)
        PyImGui.table_set_column_index(2); _rtext_colored(str(alltime_acct_total), gold)
        PyImGui.table_set_column_index(3); _rtext_colored(_runs_per_drop(_total_runs, alltime_acct_total), gold)

        PyImGui.end_table()




# ==================== AUTO SHRINE + STEP REGISTRY ====================

# Move step registry (per map)
_STEP_BY_NAME: Dict[str, int] = {}  # name -> global index
_STEP_META: List[Dict[str, Any]] = []  # {idx,name,map_id,x,y}

# â€œLearned shrinesâ€ per map (from rez positions)
_SHRINES: Dict[int, List[Tuple[float, float]]] = {}

_LAST_STEP_NAME: Optional[str] = None
_LAST_STEP_IDX: int = -1

# Tune these
SHRINE_MERGE_DIST = 450.0   # merge learned shrines within this radius
RESUME_SEARCH_DIST = 1200.0 # max dist to find a nearby move step at rez

# --- Pathing, Shrines, and Step Registry ---

def S_BlacklistModel(model_id: int):
    """Custom FSM step: add a MODEL ID to loot blacklist (script-only)."""
    from Py4GWCoreLib.Routines import Routines
    from Py4GWCoreLib.py4gwcorelib_src.Lootconfig_src import LootConfig

    def _gen():
        loot = LootConfig()
        loot.AddToBlacklist(model_id)     # <- MODEL blacklist
        yield from Routines.Yield.wait(100)
        yield
    return _gen()


def S_WhitelistModels(model_ids) -> Generator:
    from Py4GWCoreLib.Routines import Routines
    from Py4GWCoreLib.py4gwcorelib_src.Lootconfig_src import LootConfig

    def _gen():
        loot = LootConfig()
        for model_id in model_ids:
            loot.AddToWhitelist(int(model_id))
        yield from Routines.Yield.wait(100)
        yield

    return _gen()

def drop_bundle_safe(times: int = 2, delay_ms: int = 250) -> Generator:
    for _ in range(times):
        yield from Routines.Yield.Keybinds.DropBundle()
        yield from Routines.Yield.wait(delay_ms)
    yield

def _toggle_wait_for_party(enabled: bool) -> Generator:
    yield


def TrackCurrentStep(bot: "Botting") -> None:
    """Update last step name + idx (best-effort)."""
    global _LAST_STEP_NAME, _LAST_STEP_IDX

    cur = getattr(bot.config.FSM, "current_step_name", None)
    if not cur:
        cur = getattr(bot.States, "CurrentStepName", None)

    if isinstance(cur, str) and cur and cur != _LAST_STEP_NAME:
        _LAST_STEP_NAME = cur
        _LAST_STEP_IDX = _STEP_BY_NAME.get(cur, _LAST_STEP_IDX)
        ConsoleLog("STEP", f"ðŸ‘€ {cur} (idx={_LAST_STEP_IDX})")


def command_type_routine_in_message_is_active(account_email, shared_command_type):
    """Checks if a multibox command is active for an account"""
    index, message = GLOBAL_CACHE.ShMem.PreviewNextMessage(account_email)
    if index == -1 or message is None:
        return False
    if message.Command != shared_command_type:
        return False
    return True


def debug_item_signature(max_dist: float = 2500.0) -> Generator:
    agents = AgentArray.GetItemArray()
    agents = AgentArray.Filter.ByDistance(agents, Player.GetXY(), max_dist)
    agents = AgentArray.Sort.ByDistance(agents, Player.GetXY())

    ConsoleLog(BOT_NAME, f"[DBG] items_near={len(agents)}")

    for i, a in enumerate(agents[:10]):
        it = Agent.GetItemAgentByID(int(a))
        if not it:
            continue
        ConsoleLog(
            BOT_NAME,
            f"[DBG] #{i} agent_id={a} item_id={it.item_id} extra_type={it.extra_type} h00CC={hex(int(it.h00CC))}"
        )
        yield from Routines.Yield.wait(100)

    yield

INTERACTABLE_TYPES = {0x200, 0x400}  # coffres / portes / brasiers (comme ton AutoIt)


try:
    from Py4GWCoreLib import Item
except Exception:
    Item = None

TORCH_MODEL_IDS = {22341, 22342}
PICKUP_DIST = 180.0
MOVE_TIMEOUT_MS = 9000


def _log_cleaning_room() -> Generator:
    """Log message when L2 - Cleaning header state is reached."""
    ConsoleLog(BOT_NAME, "Clearing room level 2")
    yield

BOGROOT_GADGET_ID: int | None = None  # 8934 is the SoO/Fendi chest id, not a confirmed Bogroot chest id.
BOGROOT_CHEST_ENCODED_NAMES = ((2, 129, 93, 40, 137, 247, 20, 165, 34, 102, 0, 0),)
BOGROOT_SCAN_RADIUS = 700.0  # un peu plus large que 500 pour etre safe
BOGROOT_CHEST_SPAWN_TIMEOUT_MS = 30000
BOGROOT_CHEST_POLL_MS = 500


def _matches_BOGROOT_chest_encoded_name(agent_id: int) -> bool:
    try:
        encoded_name = tuple(int(value) for value in PyAgent.PyAgent.GetAgentEncName(agent_id))
    except Exception:
        return False
    return encoded_name in BOGROOT_CHEST_ENCODED_NAMES


def _target_BOGROOT_chest_agent_id() -> int:
    """Return the Bogroot chest agent near the expected chest position."""
    gadgets = AgentArray.GetGadgetArray()
    gadgets = AgentArray.Filter.ByDistance(gadgets, BOGROOT_CHEST_POSITION, BOGROOT_SCAN_RADIUS)
    gadgets = AgentArray.Sort.ByDistance(gadgets, BOGROOT_CHEST_POSITION)

    candidates = []
    for a in gadgets:
        aid = int(a)
        g = Agent.GetGadgetAgentByID(aid)
        if not g:
            continue

        try:
            candidates.append((aid, int(g.gadget_id), int(g.extra_type), _matches_BOGROOT_chest_encoded_name(aid)))
        except Exception:
            continue

    if not candidates:
        return 0

    for aid, gadget_id, extra_type, encoded_match in candidates:
        if encoded_match:
            ConsoleLog(
                BOT_NAME,
                f"Matched Bogroot Chest encoded name aid={aid} gadget_id={gadget_id} extra_type={extra_type}.",
                Py4GW.Console.MessageType.Info,
            )
            return aid

    if BOGROOT_GADGET_ID is not None:
        for aid, gadget_id, _extra_type, _encoded_match in candidates:
            if gadget_id == BOGROOT_GADGET_ID:
                return aid

    aid, gadget_id, extra_type, _encoded_match = candidates[0]
    ConsoleLog(
        BOT_NAME,
        f"Using nearest Bogroot chest gadget candidate aid={aid} gadget_id={gadget_id} extra_type={extra_type}.",
        Py4GW.Console.MessageType.Info,
    )
    return aid


def _wait_for_BOGROOT_chest_agent_id() -> Generator[Any, Any, int]:
    deadline = time.time() + (BOGROOT_CHEST_SPAWN_TIMEOUT_MS / 1000.0)
    while time.time() < deadline:
        target = _target_BOGROOT_chest_agent_id()
        if target != 0:
            return target
        yield from Routines.Yield.wait(BOGROOT_CHEST_POLL_MS)

    ConsoleLog(BOT_NAME, "Bogroot chest was not found after waiting for spawn; nearby gadget debug follows.")
    yield from debug_nearby_gadgets()
    return 0



def debug_nearby_gadgets(max_print: int = 10) -> Generator:
    """Debug rapide si jamais tu veux vÃ©rifier les candidats autour du point."""
    gadgets = AgentArray.GetGadgetArray()
    gadgets = AgentArray.Filter.ByDistance(gadgets, BOGROOT_CHEST_POSITION, BOGROOT_SCAN_RADIUS)
    gadgets = AgentArray.Sort.ByDistance(gadgets, BOGROOT_CHEST_POSITION)

    ConsoleLog(BOT_NAME, f"[BOGROOT] gadgets_near={len(gadgets)}")
    for i, a in enumerate(gadgets[:max_print]):
        aid = int(a)
        g = Agent.GetGadgetAgentByID(aid)
        if not g:
            continue
        try:
            ConsoleLog(BOT_NAME, f"[BOGROOT] #{i} aid={aid} gadget_id={int(g.gadget_id)} extra_type={int(g.extra_type)}")
        except Exception:
            ConsoleLog(BOT_NAME, f"[BOGROOT] #{i} aid={aid} (no fields)")
        yield from Routines.Yield.wait(100)
    yield

def TargetNearestNPC():
    npc_array = AgentArray.GetNPCMinipetArray()
    npc_array = AgentArray.Filter.ByDistance(npc_array,Player.GetXY(), 200)
    npc_array = AgentArray.Sort.ByDistance(npc_array, Player.GetXY())
    if len(npc_array) > 0:
        Player.ChangeTarget(npc_array[0])

CHEST_OPEN_ATTEMPTS = 3  # number of interact attempts per account

def open_BOGROOT_chest():
    """Multibox coordination for opening the final chest"""
    ConsoleLog(BOT_NAME, "Opening final chest with multibox...")

    target = yield from _wait_for_BOGROOT_chest_agent_id()
    if target == 0:
        ConsoleLog(BOT_NAME, "No Bogroot chest found near the expected chest position!")
        return

    sender_email = Player.GetAccountEmail()
    accounts = GLOBAL_CACHE.ShMem.GetAllAccountData()

    Player.ChangeTarget(target)
    yield from Routines.Yield.wait(150)

    # --- LEADER: interact multiple times to ensure chest opens ---
    for attempt in range(CHEST_OPEN_ATTEMPTS):
        ConsoleLog(BOT_NAME, f"Leader opening chest (attempt {attempt + 1}/{CHEST_OPEN_ATTEMPTS})")
        Player.Interact(target, False)
        yield from Routines.Yield.wait(500)

    # Wait for the leader to finish
    while command_type_routine_in_message_is_active(sender_email, SharedCommandType.InteractWithTarget):
        yield from Routines.Yield.wait(250)
    while command_type_routine_in_message_is_active(sender_email, SharedCommandType.PickUpLoot):
        yield from Routines.Yield.wait(1000)
    yield from Routines.Yield.wait(5000)

    # Command opening for all members with multiple attempts
    for account in accounts:
        if not account.AccountEmail or sender_email == account.AccountEmail:
            continue
        ConsoleLog(BOT_NAME, f"Ordering {account.AccountEmail} to open chest")

        for attempt in range(CHEST_OPEN_ATTEMPTS):
            ConsoleLog(BOT_NAME, f"{account.AccountEmail} attempt {attempt + 1}/{CHEST_OPEN_ATTEMPTS}")
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account.AccountEmail,
                SharedCommandType.InteractWithTarget,
                (target, 0, 0, 0),
            )
            yield from Routines.Yield.wait(1000)

        while command_type_routine_in_message_is_active(account.AccountEmail, SharedCommandType.InteractWithTarget):
            yield from Routines.Yield.wait(1000)
        while command_type_routine_in_message_is_active(account.AccountEmail, SharedCommandType.PickUpLoot):
            yield from Routines.Yield.wait(1000)
        yield from Routines.Yield.wait(5000)

    ConsoleLog(BOT_NAME, "ALL accounts opened chest!")
    yield


def resolve_BOGROOT_fight() -> Generator:
    """
    Hold near BOGROOT's position, kill all enemies in compass range,
    and require 20s stable verification with neither BOGROOT Nin
    nor Soul of BOGROOT present before finishing.
    """
    boss_model_ids = {7064, 7065} #BOGROOT Nin and Soul of BOGROOT
    anchor_x, anchor_y = (-16022.9, 17889.9)
    compass_sq = Range.Compass.value ** 2
    anchor_soft_radius_sq = 750.0 ** 2
    stable_verify_ms = 0

    while stable_verify_ms < 20000:
        if Map.GetMapID() != BOGROOT_L2:
            break
        if not Routines.Checks.Map.MapValid():
            yield from Routines.Yield.wait(500)
            continue

        player_pos = Player.GetXY()
        if not player_pos:
            yield from Routines.Yield.wait(500)
            continue

        dx_a = anchor_x - player_pos[0]
        dy_a = anchor_y - player_pos[1]
        if (dx_a * dx_a + dy_a * dy_a) > anchor_soft_radius_sq:
            Player.Move(anchor_x, anchor_y)

        nearest_id = 0
        nearest_dist_sq = float("inf")
        boss_present = False

        for agent_id in AgentArray.GetEnemyArray():
            if not Agent.IsAlive(agent_id):
                continue
            enemy_pos = Agent.GetXY(agent_id)
            if not enemy_pos:
                continue
            ax = enemy_pos[0] - anchor_x
            ay = enemy_pos[1] - anchor_y
            if (ax * ax + ay * ay) > compass_sq:
                continue
            if Agent.GetModelID(agent_id) in boss_model_ids:
                boss_present = True
            px = enemy_pos[0] - player_pos[0]
            py = enemy_pos[1] - player_pos[1]
            dist_sq = px * px + py * py
            if dist_sq < nearest_dist_sq:
                nearest_dist_sq = dist_sq
                nearest_id = agent_id

        if nearest_id:
            stable_verify_ms = 0
            Player.ChangeTarget(nearest_id)
            Player.Interact(nearest_id, True)
            target_pos = Agent.GetXY(nearest_id)
            if target_pos:
                dx = target_pos[0] - player_pos[0]
                dy = target_pos[1] - player_pos[1]
                if (dx * dx + dy * dy) > (Range.Earshot.value ** 2):
                    Player.Move(target_pos[0], target_pos[1])
        else:
            if not boss_present:
                stable_verify_ms += 500
            else:
                stable_verify_ms = 0
            Player.Move(anchor_x, anchor_y)

        yield from Routines.Yield.wait(500)

    ConsoleLog(BOT_NAME, "BOGROOT is dead -- area clear for 20s. Goodluck on chest ^.^")
    yield


# --- Wipe Recovery and Step Anchors ---

def wait_for_map_change(target_map_id, timeout_seconds=60):
    """Wait for map change with timeout"""
    ConsoleLog(BOT_NAME, f"Waiting for map change to {target_map_id}...")
    timeout = time.time() + timeout_seconds
    while True:
        current_map = Map.GetMapID()
        if current_map == target_map_id:
            ConsoleLog(BOT_NAME, f"Map change detected! Now in map {target_map_id}")
            yield
            return
        if time.time() > timeout:
            ConsoleLog(BOT_NAME, f"Timeout waiting for map {target_map_id}")
            yield
            return
        yield from Routines.Yield.wait(500)


def _on_party_wipe(bot: "Botting"):
    global L2_BOSS_ROUTE_UNLOCKED
    wipe_pos = Player.GetXY()
    if not wipe_pos:
        wipe_pos = (0.0, 0.0)

    # Wait for the dungeon wipe respawn instead of reusing whatever movement was
    # active when we died.  The movement state we jump to below will create a new
    # Mission Map-style navmesh path from the respawn shrine to the next target.
    yield from _wait_for_respawn_position_change((float(wipe_pos[0]), float(wipe_pos[1])), "wipe recovery")
    if not Routines.Checks.Map.MapValid():
        bot.config.FSM.resume()
        return

    ConsoleLog("Res Check", "Respawn confirmed; rebuilding route from current position.")
    yield from bot.Wait._coro_for_time(500)

    # Map-safe anchors (YOU said you replaced jumps by headers)
    # These should be the JUMPABLE step names (anchors), not just visual headers.
    SHRINES_BY_MAP = {
        BOGROOT_L1: [
            ("Secure return - L1", 19045.95, 7877.0),
            ("Secure return 2 - L1", 6491.41, 5310.56),
            ("Secure return 3 - L1", 141.23, -1965.14),
        ],
        BOGROOT_L2: [
            ("Secure return - L2", -11055.0, -5551.0),
            ("Secure return 2 - L2", 8591.0, 4285.0),
            ("Secure return - Boss", 19544.0, -11840.0),
        ],
    }

    def pick_nearest_anchor(map_id: int, px: float, py: float) -> str:
        candidates = SHRINES_BY_MAP.get(map_id)
        if not candidates:
            return "Reset farm"  # generic fallback anchor

        best_name = candidates[0][0]
        best_d2 = float("inf")
        for name, sx, sy in candidates:
            d2 = (px - sx) ** 2 + (py - sy) ** 2
            if d2 < best_d2:
                best_d2 = d2
                best_name = name
        return best_name

    player_x, player_y = Player.GetXY()
    map_id = int(Map.GetMapID())

    bot.config.FSM.pause()

    # Not in dungeon maps -> resign and go to generic secure return
    if map_id not in (BOGROOT_L1, BOGROOT_L2):
        bot.Multibox.ResignParty()
        yield from bot.Wait._coro_for_time(10000)
        bot.config.FSM.jump_to_state_by_name("Reset farm")
        bot.config.FSM.resume()
        return

    # Full party defeated in Bogroot respawns the party at a shrine after ~10s.
    # Do not restart the entire farm or keep the old move action; resume at the
    # nearest secure anchor so the following movement state computes a fresh path
    # from the new shrine position to the next recorded target.
    chosen = pick_nearest_anchor(map_id, float(player_x), float(player_y))

    if map_id == BOGROOT_L2:
        if L2_BOSS_ROUTE_UNLOCKED:
            chosen = "Secure return - Boss"
        else:
            chosen = pick_nearest_anchor(map_id, float(player_x), float(player_y))                          

    ConsoleLog("Res Check", f"↩ wipe-route -> {chosen} (map={map_id}, pos=({player_x:.0f},{player_y:.0f}))")
    bot.config.FSM.jump_to_state_by_name(chosen)

    bot.config.FSM.resume()
    return


def OnPartyWipe(bot: "Botting"):
    ConsoleLog("on_party_wipe", "event triggered")
    fsm = bot.config.FSM
    fsm.pause()
    fsm.AddManagedCoroutine("OnWipe_OPD", lambda: _on_party_wipe(bot))

def S_Path(name: str, points: list[tuple[float, float]], map_id: Optional[int] = None) -> None:
    bot.States.AddHeader(name)

    # âœ… Step "ancre" jumpable
    bot.States.AddCustomState(_step_anchor, name)

    AddMissionMapPath(points, name)

def UseSummons():
    """
    Uses:
    - Summons (model ID 30209)
    - Legionnary Summoning Crystal (model ID 37810)
    - Mysterious 31155
    """

    summons = [
        ("Summons", 30209),
        ("Legionnary Crystal", 37810),
        ("Mysterious", 31155),
    ]

    for name, model_id in summons:
        ConsoleLog("UseSummons", f"Searching for {name}...", log=True)

        item_id = GLOBAL_CACHE.Inventory.GetFirstModelID(model_id)

        if item_id:
            ConsoleLog("UseSummons", f"{name} found (item_id: {item_id}), using...", log=True)
            GLOBAL_CACHE.Inventory.UseItem(item_id)
            yield from Routines.Yield.wait(1000)
            ConsoleLog("UseSummons", f"{name} used!", log=True)
        else:
            ConsoleLog("UseSummons", f"{name} not found in inventory", log=True)

    yield

_RANDOM_DISTRICTS = [
    6,  # EuropeItalian
    7,  # EuropeSpanish
    8,  # EuropePolish
    9,  # EuropeRussian
]

def _coro_travel_random_district(target_map_id: int) -> Generator:
    if _randomize_district:
        district = random.choice(_RANDOM_DISTRICTS)
        ConsoleLog(BOT_NAME, f"Traveling to map {target_map_id} with random district {district}")
        Map.TravelToDistrict(target_map_id, district=district)
        yield from Routines.Yield.wait(500)
        yield from bot.Wait._coro_for_map_load(target_map_id=target_map_id)
    else:
        yield from bot.Map._coro_travel(target_map_id, "")

def _step_anchor() -> Generator:
    yield

def loop_marker():
    """Empty marker for loop restart point"""
    ConsoleLog(BOT_NAME, "Starting new dungeon run...")
    yield

def apply_widget_policy_step() -> Generator:
    bot.Multibox.ApplyWidgetPolicy(
        enable_widgets=WIDGETS_TO_ENABLE,
        disable_widgets=WIDGETS_TO_DISABLE,
        apply_local=True,
    )
    yield from _disable_widgets_on_alts_only(_ALT_ONLY_DISABLE_WIDGETS)
    yield


def _force_leader_hero_ai_combat() -> Generator:
    """Make startup deterministic when the leader's HeroAI combat toggle was left off."""
    bot.ResetHeroAICombatState(
        active=True,
        following=True,
        targeting=True,
        combat=True,
        skills=True,
    )
    ConsoleLog(BOT_NAME, "Leader HeroAI combat/options forced ON.", Py4GW.Console.MessageType.Info)
    yield from Routines.Yield.wait(250)
    yield


def _set_dungeon_looting(enabled: bool, reason: str = "") -> Generator:
    """Disable LootManager/auto-loot during the Sparkfly run, re-enable inside Bogroot."""
    enabled = bool(enabled)
    action = SharedCommandType.EnableWidget if enabled else SharedCommandType.DisableWidget
    widget_handler = get_widget_handler()

    if enabled:
        if not widget_handler.is_widget_enabled("LootManager"):
            widget_handler.enable_widget("LootManager")
        bot.Properties.ApplyNow("auto_loot", "active", True)
        bot.ResetHeroAICombatState(active=True, following=True, targeting=True, combat=True, looting=True, skills=True)
    else:
        if widget_handler.is_widget_enabled("LootManager"):
            widget_handler.disable_widget("LootManager")
        bot.Properties.ApplyNow("auto_loot", "active", False)
        bot.ResetHeroAICombatState(active=True, following=True, targeting=True, combat=True, looting=False, skills=True)

    sender_email = Player.GetAccountEmail()
    if sender_email:
        for account in GLOBAL_CACHE.ShMem.GetAllAccountData():
            account_email = getattr(account, "AccountEmail", "")
            if not account_email or account_email == sender_email:
                continue
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account_email,
                action,
                (0, 0, 0, 0),
                ("LootManager", "", "", ""),
            )

    ConsoleLog(
        BOT_NAME,
        f"Looting {'enabled' if enabled else 'disabled'} ({reason}).",
        Py4GW.Console.MessageType.Info,
    )
    yield from Routines.Yield.wait(500)
    yield

# --- Settings and Bot UI Helpers ---

def _draw_difficulty_setting() -> None:
    import PyImGui
    global _use_hard_mode

    _ensure_ini_initialized()
    new_hard_mode = PyImGui.checkbox("Hard Mode (HM)", _use_hard_mode)
    if new_hard_mode != _use_hard_mode:
        _use_hard_mode = new_hard_mode
        _save_settings()

def _draw_district_setting() -> None:
    import PyImGui
    global _randomize_district

    _ensure_ini_initialized()
    new_val = PyImGui.checkbox("Randomize EU District", _randomize_district)
    if new_val != _randomize_district:
        _randomize_district = new_val
        _save_settings()

def _use_all_consumables_now() -> None:
    try:
        from Py4GWCoreLib.routines_src.behaviourtrees_src.botting_consumables import consumable_specs
        from Py4GWCoreLib.routines_src.behaviourtrees_src.botting_consumables import send_consumable_to_accounts
        from Py4GWCoreLib.routines_src.behaviourtrees_src.botting_consumables import use_local_consumable

        for model_id, effect_name in consumable_specs("all"):
            effect_id = int(GLOBAL_CACHE.Skill.GetID(effect_name) or 0)
            use_local_consumable(int(model_id), effect_id)
            send_consumable_to_accounts(int(model_id), effect_id)
        ConsoleLog(BOT_NAME, "Use all consumables requested for leader and alts.", Py4GW.Console.MessageType.Info)
    except Exception as exc:
        ConsoleLog(BOT_NAME, f"Use all consumables failed: {exc}", Py4GW.Console.MessageType.Error)


def _precons_enabled_for_phase(phase: str) -> bool:
    if phase == "running":
        return _use_precons_running
    if phase == "level1":
        return _use_precons_level1
    if phase == "level2":
        return _use_precons_level2
    return False


def _use_precons_if_enabled(phase: str, context: str = "") -> Generator:
    _ensure_ini_initialized()
    if not _precons_enabled_for_phase(phase):
        suffix = f" {context}" if context else ""
        ConsoleLog(BOT_NAME, f"Skipping precons{suffix}: {phase} precons disabled in settings.", Py4GW.Console.MessageType.Info)
        yield
        return

    _use_all_consumables_now()
    yield from Routines.Yield.wait(1000)


def _draw_consumable_button() -> None:
    import PyImGui
    global _use_precons_running, _use_precons_level1, _use_precons_level2

    _ensure_ini_initialized()
    PyImGui.text("Use precons automatically:")

    new_running = PyImGui.checkbox("Running to dungeon##froggy_precons_running", _use_precons_running)
    if new_running != _use_precons_running:
        _use_precons_running = new_running
        _save_settings()

    new_l1 = PyImGui.checkbox("Level 1##froggy_precons_l1", _use_precons_level1)
    if new_l1 != _use_precons_level1:
        _use_precons_level1 = new_l1
        _save_settings()

    new_l2 = PyImGui.checkbox("Level 2##froggy_precons_l2", _use_precons_level2)
    if new_l2 != _use_precons_level2:
        _use_precons_level2 = new_l2
        _save_settings()

    if PyImGui.button("Use all consumables now##froggy_recorded_use_cons"):
        _use_all_consumables_now()

def _draw_merchant_settings() -> None:
    import PyImGui
    global _merchant_enabled, _merchant_id_kits_target, _merchant_salvage_kits_target, _inventory_slots_threshold, _merchant_store_consumable_materials, _merchant_sell_materials, _merchant_sell_rare_mats, _merchant_buy_ectos, _merchant_ecto_threshold, _merchant_alt_wait_ms

    _ensure_ini_initialized()

    PyImGui.separator()
    PyImGui.text("Merchant (Guild Hall) — runs once on startup")
    PyImGui.separator()

    new_enabled = PyImGui.checkbox("Restock kits / sell materials on startup", _merchant_enabled)
    if new_enabled != _merchant_enabled:
        _merchant_enabled = new_enabled
        _save_settings()

    if _merchant_enabled:
        PyImGui.push_item_width(100)
        new_id = PyImGui.input_int("ID Kits target##froggy_id", _merchant_id_kits_target)
        if new_id != _merchant_id_kits_target:
            _merchant_id_kits_target = max(0, new_id)
            _save_settings()

        new_sal = PyImGui.input_int("Salvage Kits target##froggy_sal", _merchant_salvage_kits_target)
        if new_sal != _merchant_salvage_kits_target:
            _merchant_salvage_kits_target = max(0, new_sal)
            _save_settings()

        new_inv = PyImGui.input_int("Free Inventory Slots target##froggy_inv_thresh", _inventory_slots_threshold)
        if new_inv != _inventory_slots_threshold:
            _inventory_slots_threshold = max(0, new_inv)
            _save_settings()
        PyImGui.pop_item_width()

        new_sell = PyImGui.checkbox("Sell common materials##froggy_sell", _merchant_sell_materials)
        if new_sell != _merchant_sell_materials:
            _merchant_sell_materials = new_sell
            _save_settings()

        new_store = PyImGui.checkbox(
            "Store consumable materials (Dust/Iron/Feather/Bone/Fiber)##froggy_store_cons_mats",
            _merchant_store_consumable_materials,
        )
        if new_store != _merchant_store_consumable_materials:
            _merchant_store_consumable_materials = new_store
            _save_settings()

        new_rare = PyImGui.checkbox("Sell Diamond & Onyx to Rare Material Trader##froggy_rare_mats", _merchant_sell_rare_mats)
        if new_rare != _merchant_sell_rare_mats:
            _merchant_sell_rare_mats = new_rare
            _save_settings()

        new_ectos = PyImGui.checkbox("Buy Glob of Ectoplasm when storage over threshold##froggy_ectos", _merchant_buy_ectos)
        if new_ectos != _merchant_buy_ectos:
            _merchant_buy_ectos = new_ectos
            _save_settings()

        if _merchant_buy_ectos:
            new_thresh = PyImGui.input_int("Storage threshold (gold)##froggy_ecto_thresh", _merchant_ecto_threshold)
            if new_thresh != _merchant_ecto_threshold:
                _merchant_ecto_threshold = max(0, new_thresh)
                _save_settings()

        PyImGui.push_item_width(100)
        new_wait = PyImGui.input_int("Alt settle wait (ms)##froggy_alt_wait", _merchant_alt_wait_ms)
        if new_wait != _merchant_alt_wait_ms:
            _merchant_alt_wait_ms = max(0, min(_MAX_ALT_SETTLE_WAIT_MS, new_wait))
            _save_settings()
        PyImGui.pop_item_width()
        PyImGui.same_line(0, 6)
        PyImGui.text("(time given to alts to reach NPCs and finish)")



def _draw_froggy_settings() -> None:
    import PyImGui
    PyImGui.text("Froggy Settings")
    PyImGui.separator()
    _draw_difficulty_setting()
    _draw_district_setting()
    _draw_consumable_button()
    _draw_merchant_settings()

# ==================== INITIALIZATION ====================

bot.SetMainRoutine(farm_froggy_routine)
bot.UI.override_draw_config(_draw_froggy_settings)


# ==================== UI AND ENTRYPOINT ====================

def _draw_froggy_window_with_stats_tab() -> None:
    import PyImGui
    from Py4GWCoreLib import ImGui, IniManager, Routines

    main_child_dimensions = (500, 350)
    iconwidth = 96

    if not bot.config.ini_key_initialized:
        bot.config.ini_key = IniManager().ensure_key(
            f"BottingClass/bot_{bot.config.bot_name}",
            f"bot_{bot.config.bot_name}.ini",
        )
        IniManager().load_once(bot.config.ini_key)
        bot.config.ini_key_initialized = True
        _ensure_ini_initialized()

    if not bot.config.ini_key:
        return

    if ImGui.Begin(
        ini_key=bot.config.ini_key,
        name=bot.config.bot_name,
        p_open=True,
        flags=PyImGui.WindowFlags.AlwaysAutoResize,
    ):
        if PyImGui.begin_tab_bar(bot.config.bot_name + "_tabs"):
            if PyImGui.begin_tab_item("Main"):
                if PyImGui.begin_child(f"{bot.config.bot_name} - Main", main_child_dimensions, True, PyImGui.WindowFlags.NoFlag):
                    bot.UI._draw_main_child(main_child_dimensions, TEXTURE, iconwidth)
                    PyImGui.end_child()
                PyImGui.end_tab_item()

            if PyImGui.begin_tab_item("Navigation"):
                PyImGui.text("Jump to step (filtered by step index):")
                bot.UI._draw_fsm_jump_button()
                PyImGui.separator()
                bot.UI.draw_fsm_tree_selector_ranged(child_size=main_child_dimensions)
                PyImGui.end_tab_item()

            if PyImGui.begin_tab_item("Settings"):
                bot.UI._draw_settings_child()
                PyImGui.end_tab_item()

            if PyImGui.begin_tab_item("Help"):
                bot.UI._draw_help_child()
                PyImGui.end_tab_item()

            if PyImGui.begin_tab_item("Debug"):
                bot.UI.draw_debug_window()
                PyImGui.end_tab_item()

            if PyImGui.begin_tab_item("Statistics"):
                _draw_froggy_stats()
                PyImGui.end_tab_item()

            PyImGui.end_tab_bar()

    ImGui.End(bot.config.ini_key)

    if Routines.Checks.Map.MapValid():
        bot.UI.DrawPath(
            bot.config.config_properties.follow_path_color.get("value"),
            bot.config.config_properties.use_occlusion.is_active(),
            bot.config.config_properties.snap_to_ground_segments.get("value"),
            bot.config.config_properties.floor_offset.get("value"),
        )

def tooltip():
    import PyImGui
    from Py4GWCoreLib import ImGui, Color
    PyImGui.begin_tooltip()

    # Title
    title_color = Color(255, 200, 100, 255)
    ImGui.push_font("Regular", 20)
    PyImGui.text_colored("Frog Scepter Farmer bot", title_color.to_tuple_normalized())
    ImGui.pop_font()
    PyImGui.spacing()
    PyImGui.separator()
    # Description
    PyImGui.text("multi-account bot to farm Frog Scepter")
    PyImGui.spacing()
    PyImGui.bullet_text("Requirements:")
    PyImGui.bullet_text("- Any number of accounts, but for best performance, 8 well-geared accounts is recommended")
    PyImGui.bullet_text("- HeroAI widget enabled on all accounts")
    PyImGui.bullet_text("- Launch the script on the party leader only")
    PyImGui.bullet_text("Designed for Normal Mode (NM) and Hard Mode (HM), check bot settings for more details.")
    
    # Credits
    PyImGui.text_colored("Credits:", title_color.to_tuple_normalized())
    PyImGui.bullet_text("Developed by Oo SKY oO")
    PyImGui.bullet_text("Contributors: Wick-Divinus, Sloppynacho, XLeek, Yods, Le Z, NotNobu")
    PyImGui.end_tooltip()

def main():
    bot.Update()
    _write_settings()
    draw_window_sig = inspect.signature(bot.UI.draw_window)
    if "extra_tabs" in draw_window_sig.parameters:
        bot.UI.draw_window(
            icon_path=TEXTURE,
            main_child_dimensions=(500, 350),
            extra_tabs=[("Statistics", _draw_froggy_stats)],
        )
    else:
        _draw_froggy_window_with_stats_tab()


if __name__ == "__main__":
    main()
