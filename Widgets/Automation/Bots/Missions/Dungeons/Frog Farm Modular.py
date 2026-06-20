"""Dedicated launcher for the modular Frog Farm recipe scaffold."""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any

import PyImGui

from Py4GWCoreLib import Agent
from Py4GWCoreLib import Console
from Py4GWCoreLib import ConsoleLog
from Py4GWCoreLib import GLOBAL_CACHE
from Py4GWCoreLib import Map
from Py4GWCoreLib import Player
from Py4GWCoreLib import Quest
from Py4GWCoreLib import SharedCommandType
from Py4GWCoreLib.GlobalCache.shared_memory_src.Globals import SHMEM_MAX_NUMBER_OF_SKILLS
from Py4GWCoreLib.GlobalCache.shared_memory_src.HeroAIOptionStruct import HeroAIOptionStruct
from Py4GWCoreLib.modular import BTRecipeRunner
from Py4GWCoreLib.modular import RecipeSpec
from Py4GWCoreLib.modular.paths import modular_data_root
from Py4GWCoreLib.modular.widget_runtime import guarded_widget_main
from Py4GW_widget_manager import get_widget_handler


MODULE_NAME = "Frog Farm Modular"
MODULE_ICON = "Textures\\Module_Icons\\Bogroot Growths.png"
MODULE_TAGS = ["Frog Scepter", "Bogroot", "Dungeon", "modular_bot"]

RECIPE_KIND = "dungeon"
RECIPE_KEY = "frog_farm_modular"
RECIPE_TITLE = "Frog Farm Modular"
RECIPE_RELATIVE_PATH = Path("dungeons") / f"{RECIPE_KEY}.json"

GOOD = (0.42, 0.88, 0.55, 1.0)
WARN = (1.00, 0.78, 0.32, 1.0)
BAD = (1.00, 0.38, 0.38, 1.0)
MUTED = (0.62, 0.66, 0.70, 1.0)

WIDGETS_TO_ENABLE: tuple[str, ...] = (
    "HeroAI",
    "LootManager",
    "Return to outpost on defeat",
)
WIDGETS_TO_DISABLE: tuple[str, ...] = ()
ALT_ONLY_DISABLE_WIDGETS: tuple[str, ...] = (
    MODULE_NAME,
    "Frog Farm Modular",
    "Frog Scepter bot",
    "Frog Scepter",
    "Bogroot Growths",
)

BOGROOT_L1 = 615
BOGROOT_L2 = 616
TEKKS_WAR_QUEST_ID = 0x339
REVIVE_TELEPORT_DISTANCE = 1250.0
REVIVE_SETTLE_MS = 3000.0

RECOVERY_ANCHORS_BY_MAP: dict[int, tuple[tuple[str, float, float], ...]] = {
    BOGROOT_L1: (
        ("Level 1 blessing approach", 19045.95, 7877.0),
        ("Level 1 clear to level 2 portal", 6491.41, 5310.56),
    ),
    BOGROOT_L2: (
        ("Take level 2 entry Dwarven blessing", -11055.0, -5551.0),
        ("Level 2 first route", -955.0, 10984.0),
        ("Take Beacon of Droknar blessing", 8591.0, 4285.0),
        ("Level 2 boss lock approach", 16686.0, -5886.0),
        ("Open boss lock", 17867.55, -6250.63),
        ("Take final Beacon of Droknar blessing", 19619.0, -11498.0),
        ("Level 2 boss and chest approach", 16017.74, -19040.79),
    ),
}

_runner: BTRecipeRunner | None = None
_loop = False
_debug_logging = False
_apply_widget_policy_on_start = True
_use_hard_mode = True
_start_step_index = 0
_preview_step_index = 0
_status = "Scaffold ready"
_death_seen = False
_death_pos: tuple[float, float] | None = None
_death_map_id = 0
_revive_seen_ms = 0.0


def _recipe_path() -> Path:
    return Path(modular_data_root()) / RECIPE_RELATIVE_PATH


def _load_recipe() -> dict[str, Any]:
    try:
        data = json.loads(_recipe_path().read_text(encoding="utf-8-sig"))
    except Exception as exc:
        return {"error": str(exc), "steps": [], "todo_sections": []}
    return data if isinstance(data, dict) else {"steps": [], "todo_sections": []}


def _recipe_steps() -> list[dict[str, Any]]:
    steps = _load_recipe().get("steps", [])
    return [step for step in steps if isinstance(step, dict)] if isinstance(steps, list) else []


def _has_route_steps() -> bool:
    return any(str(step.get("type") or "").strip().lower() == "route" for step in _recipe_steps())


def _step_label(step: dict[str, Any], index: int) -> str:
    title = str(step.get("name") or "").strip() or "Step"
    step_type = str(step.get("type") or "").strip()
    action = str(step.get("action") or step.get("mode") or "").strip()
    detail = ".".join(part for part in (step_type, action) if part)
    anchor = " [anchor]" if bool(step.get("anchor")) else ""
    suffix = f" ({detail})" if detail else ""
    return f"{index + 1:02d}. {title}{suffix}{anchor}"


def _todo_sections() -> list[dict[str, Any]]:
    sections = _load_recipe().get("todo_sections", [])
    return [section for section in sections if isinstance(section, dict)] if isinstance(sections, list) else []


def _debug(message: str) -> None:
    if _debug_logging:
        ConsoleLog(MODULE_NAME, message, Console.MessageType.Info)


def _build_runner() -> BTRecipeRunner:
    return BTRecipeRunner(
        MODULE_NAME,
        [RecipeSpec(kind=RECIPE_KIND, key=RECIPE_KEY, title=RECIPE_TITLE)],
        start_step_index=_start_step_index,
        loop=_loop,
        headless_heroai_enabled=False,
        suppress_party_wipe_recovery=True,
        debug_hook=_debug,
    )


def _start_runner() -> None:
    global _runner, _status
    if not _has_route_steps():
        _status = "Recipe scaffold has no route steps yet"
        return
    try:
        if _apply_widget_policy_on_start:
            _apply_multibox_widget_policy()
        _apply_frog_startup_setup()
        _runner = _build_runner()
        _runner.start()
        _status = "Running"
    except Exception as exc:
        _runner = None
        _status = f"Start failed: {exc}"
        ConsoleLog(MODULE_NAME, _status, Console.MessageType.Error)


def _stop_runner() -> None:
    global _runner, _status
    if _runner is not None:
        _runner.stop()
    _runner = None
    _status = "Stopped"


def _update_runner() -> None:
    global _runner, _status
    if _runner is None:
        return
    try:
        _update_death_recovery()
        if _runner is None:
            return
        _runner.update()
        if not _runner.is_running() and not _runner.is_paused():
            _status = "Completed"
    except Exception as exc:
        _status = f"Runner error: {exc}"
        _runner = None
        ConsoleLog(MODULE_NAME, _status, Console.MessageType.Error)


def _draw_controls() -> None:
    global _loop, _debug_logging, _apply_widget_policy_on_start, _use_hard_mode, _status
    recipe_has_routes = _has_route_steps()
    if recipe_has_routes:
        if PyImGui.button("Start##frog_modular_start"):
            _start_runner()
    else:
        PyImGui.text_colored("Start locked", WARN)

    PyImGui.same_line(0, 8)
    if PyImGui.button("Stop##frog_modular_stop"):
        _stop_runner()

    PyImGui.same_line(0, 8)
    if _runner is not None and _runner.is_running():
        if PyImGui.button("Pause##frog_modular_pause"):
            _runner.pause()
            _status = "Paused"
    elif _runner is not None and _runner.is_paused():
        if PyImGui.button("Resume##frog_modular_resume"):
            _runner.resume()
            _status = "Running"
    else:
        PyImGui.text_colored("Idle", MUTED)

    _loop = PyImGui.checkbox("Loop##frog_modular_loop", _loop)
    _debug_logging = PyImGui.checkbox("Debug log##frog_modular_debug", _debug_logging)
    _apply_widget_policy_on_start = PyImGui.checkbox(
        "Apply Frog Scepter widget policy on start##frog_modular_widget_policy",
        _apply_widget_policy_on_start,
    )
    _use_hard_mode = PyImGui.checkbox("Hard Mode##frog_modular_hard_mode", _use_hard_mode)


def _draw_step_selector() -> None:
    global _preview_step_index, _start_step_index
    steps = _recipe_steps()
    if not steps:
        return

    if _start_step_index >= len(steps):
        _start_step_index = max(0, len(steps) - 1)
    if _preview_step_index >= len(steps):
        _preview_step_index = max(0, len(steps) - 1)

    PyImGui.separator()
    PyImGui.text("Start point")
    PyImGui.text_colored(_step_label(steps[_start_step_index], _start_step_index), GOOD)
    PyImGui.text_colored("Click a row to select where the next Start begins.", MUTED)

    running_or_paused = _runner is not None and (_runner.is_running() or _runner.is_paused())
    if PyImGui.begin_child("##frog_modular_steps", (0, 170), True, PyImGui.WindowFlags.HorizontalScrollbar):
        for index, step in enumerate(steps):
            selected = index == _preview_step_index
            label = _step_label(step, index)
            if index == _start_step_index:
                label = f"[start] {label}"
            if PyImGui.selectable(
                f"{label}##frog_modular_step_{index}",
                selected,
                int(PyImGui.SelectableFlags.SpanAllColumns),
                [0.0, 0.0],
            ):
                _preview_step_index = index
                if not running_or_paused:
                    _start_step_index = index
    PyImGui.end_child()


def _draw_status() -> None:
    recipe = _load_recipe()
    steps = _recipe_steps()
    route_steps = sum(1 for step in steps if str(step.get("type") or "").strip().lower() == "route")
    color = GOOD if route_steps else WARN

    PyImGui.separator()
    PyImGui.text_colored(_status, color)
    PyImGui.text(f"Recipe: {RECIPE_RELATIVE_PATH.as_posix()}")
    PyImGui.text(f"Steps: {len(steps)} total, {route_steps} route")

    error = str(recipe.get("error") or "")
    if error:
        PyImGui.text_colored(error, BAD)

    if _runner is not None:
        phase_index, phase_total, phase_title = _runner.get_phase_progress()
        step_index, step_total, _recipe_title, step_title = _runner.get_step_progress()
        PyImGui.text(f"Phase: {phase_index}/{phase_total} {phase_title}")
        PyImGui.text(f"Step: {step_index}/{step_total} {step_title}")


def _distance_sq(a: tuple[float, float], b: tuple[float, float]) -> float:
    dx = float(a[0]) - float(b[0])
    dy = float(a[1]) - float(b[1])
    return dx * dx + dy * dy


def _nearest_recovery_step(map_id: int, pos: tuple[float, float]) -> str:
    anchors = RECOVERY_ANCHORS_BY_MAP.get(int(map_id), ())
    if not anchors:
        return ""

    best_title = anchors[0][0]
    best_dist_sq = float("inf")
    for title, anchor_x, anchor_y in anchors:
        dist_sq = _distance_sq(pos, (anchor_x, anchor_y))
        if dist_sq < best_dist_sq:
            best_title = title
            best_dist_sq = dist_sq
    return best_title


def _update_death_recovery() -> None:
    global _death_seen, _death_pos, _death_map_id, _revive_seen_ms, _status
    if _runner is None or not (_runner.is_running() or _runner.is_paused()):
        _death_seen = False
        _death_pos = None
        _death_map_id = 0
        _revive_seen_ms = 0.0
        return

    player_id = Player.GetAgentID()
    if not Agent.IsValid(player_id):
        return

    raw_pos = Player.GetXY()
    if not raw_pos or len(raw_pos) < 2:
        return
    player_pos = (float(raw_pos[0]), float(raw_pos[1]))
    map_id = int(Map.GetMapID() or 0)
    if Agent.IsDead(player_id):
        if not _death_seen:
            _death_pos = player_pos
            _death_map_id = map_id
            _revive_seen_ms = 0.0
        _death_seen = True
        return

    if not _death_seen:
        return

    if map_id not in RECOVERY_ANCHORS_BY_MAP:
        _death_seen = False
        _death_pos = None
        _death_map_id = 0
        _revive_seen_ms = 0.0
        return

    death_pos = _death_pos
    if death_pos is not None and _distance_sq(player_pos, death_pos) <= REVIVE_TELEPORT_DISTANCE * REVIVE_TELEPORT_DISTANCE:
        _death_seen = False
        _death_pos = None
        _death_map_id = 0
        _revive_seen_ms = 0.0
        return

    now_ms = time.monotonic() * 1000.0
    if _revive_seen_ms <= 0.0:
        _revive_seen_ms = now_ms
        return
    if now_ms - _revive_seen_ms < REVIVE_SETTLE_MS:
        return

    recovery_step = _nearest_recovery_step(map_id, player_pos)
    if recovery_step and _runner.restart_from_step_title(recovery_step):
        _status = f"Recovered after death: {recovery_step}"
        ConsoleLog(
            MODULE_NAME,
            (
                f"Death recovery restarted from {recovery_step!r} "
                f"(death_map={_death_map_id}, current_map={map_id}, pos=({player_pos[0]:.0f}, {player_pos[1]:.0f}))."
            ),
            Console.MessageType.Warning,
        )

    _death_seen = False
    _death_pos = None
    _death_map_id = 0
    _revive_seen_ms = 0.0


def _start_index_for_step(step_name: str) -> int:
    target = str(step_name or "").strip().casefold()
    for index, step in enumerate(_recipe_steps()):
        if str(step.get("name") or "").strip().casefold() == target:
            return index
    return -1


def _should_abandon_tekks_on_start() -> bool:
    take_quest_index = _start_index_for_step("Take quest from Tekks")
    if take_quest_index < 0:
        return _start_step_index == 0
    return _start_step_index <= take_quest_index


def _apply_frog_startup_setup() -> None:
    if _use_hard_mode and Map.IsOutpost():
        GLOBAL_CACHE.Party.SetHardMode()

    if not _should_abandon_tekks_on_start():
        return

    Quest.AbandonQuest(TEKKS_WAR_QUEST_ID)
    sender_email = str(Player.GetAccountEmail() or "").strip()
    if not sender_email:
        return

    for account_email in _iter_alt_account_emails(sender_email):
        GLOBAL_CACHE.ShMem.SendMessage(
            sender_email,
            account_email,
            SharedCommandType.AbandonQuest,
            (TEKKS_WAR_QUEST_ID, 0, 0, 0),
        )


def _email_key(email: str | None) -> str:
    return str(email or "").strip().casefold()


def _reset_local_hero_ai_combat_state(active: bool = True) -> None:
    account_email = str(Player.GetAccountEmail() or "").strip()
    if not account_email:
        return

    options = GLOBAL_CACHE.ShMem.GetHeroAIOptionsFromEmail(account_email) or HeroAIOptionStruct()
    options.Following = bool(active)
    options.Avoidance = bool(active)
    options.Looting = bool(active)
    options.Targeting = bool(active)
    options.Combat = bool(active)
    for skill_index in range(SHMEM_MAX_NUMBER_OF_SKILLS):
        options.Skills[skill_index] = bool(active)
    GLOBAL_CACHE.ShMem.SetHeroAIOptionsByEmail(account_email, options)


def _iter_alt_account_emails(sender_email: str) -> list[str]:
    sender_key = _email_key(sender_email)
    if not sender_key:
        return []

    alt_emails: list[str] = []
    for account in GLOBAL_CACHE.ShMem.GetAllAccountData() or []:
        account_email = str(getattr(account, "AccountEmail", "") or "").strip()
        if not account_email or _email_key(account_email) == sender_key:
            continue
        alt_emails.append(account_email)
    return alt_emails


def _apply_multibox_widget_policy() -> None:
    widget_handler = get_widget_handler()
    for widget_name in WIDGETS_TO_ENABLE:
        if not widget_handler.is_widget_enabled(widget_name):
            widget_handler.enable_widget(widget_name)
        if widget_name == "HeroAI":
            _reset_local_hero_ai_combat_state(active=True)
    for widget_name in WIDGETS_TO_DISABLE:
        if widget_handler.is_widget_enabled(widget_name):
            widget_handler.disable_widget(widget_name)
        if widget_name == "HeroAI":
            _reset_local_hero_ai_combat_state(active=False)

    sender_email = str(Player.GetAccountEmail() or "").strip()
    if not sender_email:
        ConsoleLog(
            MODULE_NAME,
            "Skipped alt widget policy because the sender account email is unavailable.",
            Console.MessageType.Warning,
        )
        return

    alt_emails = _iter_alt_account_emails(sender_email)
    for account_email in alt_emails:
        for widget_name in WIDGETS_TO_ENABLE:
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account_email,
                SharedCommandType.EnableWidget,
                (0, 0, 0, 0),
                (widget_name, "", "", ""),
            )
        for widget_name in ALT_ONLY_DISABLE_WIDGETS:
            GLOBAL_CACHE.ShMem.SendMessage(
                sender_email,
                account_email,
                SharedCommandType.DisableWidget,
                (0, 0, 0, 0),
                (widget_name, "", "", ""),
            )

    ConsoleLog(
        MODULE_NAME,
        f"Applied Frog Scepter widget policy to main and {len(alt_emails)} alt account(s).",
        Console.MessageType.Info,
    )


def _draw_todo() -> None:
    PyImGui.separator()
    PyImGui.text("Missing route data")
    for section in _todo_sections():
        title = str(section.get("title") or section.get("key") or "Section")
        PyImGui.text_colored(title, MUTED)
        needed = section.get("needed", [])
        if not isinstance(needed, list):
            continue
        for item in needed:
            PyImGui.bullet_text(str(item))


def _draw_window() -> None:
    PyImGui.set_next_window_size((430, 420))
    if not PyImGui.begin(MODULE_NAME):
        PyImGui.end()
        return
    PyImGui.text(MODULE_NAME)
    _draw_controls()
    _draw_status()
    _draw_step_selector()
    _draw_todo()
    PyImGui.end()


def _main_impl() -> None:
    _update_runner()
    _draw_window()


def main() -> None:
    guarded_widget_main(MODULE_NAME, _main_impl)


def tooltip() -> None:
    PyImGui.begin_tooltip()
    PyImGui.text(MODULE_NAME)
    PyImGui.separator()
    PyImGui.text("Modular scaffold for the Frog Scepter farm.")
    PyImGui.end_tooltip()


if __name__ == "__main__":
    main()
