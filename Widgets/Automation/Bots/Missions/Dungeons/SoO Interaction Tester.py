from typing import Callable
from typing import Generator
from typing import Optional
from typing import TypedDict

import time

import Py4GW
import PyImGui
import PyInventory

from Py4GWCoreLib import Agent
from Py4GWCoreLib import AgentArray
from Py4GWCoreLib import ConsoleLog
from Py4GWCoreLib import GLOBAL_CACHE
from Py4GWCoreLib import ImGui
from Py4GWCoreLib import Map
from Py4GWCoreLib import Player
from Py4GWCoreLib import Routines
from Py4GWCoreLib import SharedCommandType


MODULE_NAME = 'SoO Interaction Tester'
MODULE_CATEGORY = 'Automation'
MODULE_TAGS = ('Automation', 'Bots', 'Missions', 'Dungeons', 'Shards of Orr', 'BDS', 'Tester')
OPTIONAL = True

BOT_NAME = MODULE_NAME

DWARVEN_BLESSING_DIALOG = 0x84
SHANDRA_TAKE_DIALOG = 0x832401
SHANDRA_REWARD_DIALOG = 0x832407

TORCH_MODEL_IDS = {22341, 22342}
FENDI_CHEST_GADGET_ID = 8934
DEFAULT_SCAN_DISTANCE = 2500.0
DEFAULT_XY_TOLERANCE = 220.0


class Interaction(TypedDict):
    label: str
    kind: str
    x: Optional[float]
    y: Optional[float]
    dialog_id: Optional[int]


INTERACTIONS: list[Interaction] = [
    {
        'label': 'Arbor Bay blessing NPC',
        'kind': 'npc_dialog',
        'x': None,
        'y': None,
        'dialog_id': DWARVEN_BLESSING_DIALOG,
    },
    {'label': 'Shandra quest NPC', 'kind': 'npc', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Level 1 blessing NPC', 'kind': 'npc_dialog', 'x': None, 'y': None, 'dialog_id': DWARVEN_BLESSING_DIALOG},
    {'label': 'Level 1 door gadget', 'kind': 'gadget', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Level 2 blessing NPC', 'kind': 'npc_dialog', 'x': None, 'y': None, 'dialog_id': DWARVEN_BLESSING_DIALOG},
    {'label': 'Level 2 torch chest', 'kind': 'gadget', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Level 2 door gadget', 'kind': 'gadget', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Level 3 blessing NPC', 'kind': 'npc_dialog', 'x': None, 'y': None, 'dialog_id': DWARVEN_BLESSING_DIALOG},
    {'label': 'Level 3 torch chest', 'kind': 'gadget', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Level 3 boss door gadget', 'kind': 'gadget', 'x': None, 'y': None, 'dialog_id': None},
    {'label': 'Fendi chest', 'kind': 'fendi_chest', 'x': None, 'y': None, 'dialog_id': None},
]

window = ImGui.WindowModule(
    MODULE_NAME,
    window_name=MODULE_NAME,
    window_size=(430, 680),
    window_flags=PyImGui.WindowFlags.AlwaysAutoResize,
)

_custom_x: float = 0.0
_custom_y: float = 0.0
_custom_dialog_id: int = DWARVEN_BLESSING_DIALOG
_custom_scan_distance: float = DEFAULT_SCAN_DISTANCE
_send_to_alts: bool = False
_selected_interaction: int = 0
_last_status: str = 'Ready.'


def _set_status(message: str) -> None:
    global _last_status
    _last_status = message
    ConsoleLog(BOT_NAME, message, Py4GW.Console.MessageType.Info)


def _queue(label: str, routine_factory: Callable[[], Generator]) -> None:
    try:
        GLOBAL_CACHE.Coroutines.append(routine_factory())
        _set_status(f'Queued: {label}')
    except Exception as exc:
        ConsoleLog(BOT_NAME, f'Failed to queue {label}: {exc}', Py4GW.Console.MessageType.Error)


def _xy_ready(interaction: Interaction) -> bool:
    return interaction['x'] is not None and interaction['y'] is not None


def _parse_xy(interaction: Interaction) -> tuple[float, float]:
    return float(interaction['x'] or 0.0), float(interaction['y'] or 0.0)


def _move_to_xy(x: float, y: float, tolerance: float = DEFAULT_XY_TOLERANCE, timeout_ms: int = 15000) -> Generator:
    start = time.time() * 1000.0
    while True:
        px, py = Player.GetXY()
        if ((px - x) ** 2 + (py - y) ** 2) ** 0.5 <= tolerance:
            break
        if (time.time() * 1000.0) - start > timeout_ms:
            ConsoleLog(BOT_NAME, f'Move timeout at ({x:.0f}, {y:.0f})', Py4GW.Console.MessageType.Warning)
            break
        Player.Move(x, y)
        yield from Routines.Yield.wait(100)
    yield


def _send_to_alts_interact_target(target_id: int) -> None:
    sender_email = Player.GetAccountEmail()
    for account in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if not account.AccountEmail or account.AccountEmail == sender_email:
            continue
        GLOBAL_CACHE.ShMem.SendMessage(
            sender_email,
            account.AccountEmail,
            SharedCommandType.InteractWithTarget,
            (int(target_id), 0, 0, 0),
        )


def _send_to_alts_dialog(target_id: int, dialog_id: int) -> None:
    sender_email = Player.GetAccountEmail()
    for account in GLOBAL_CACHE.ShMem.GetAllAccountData():
        if not account.AccountEmail or account.AccountEmail == sender_email:
            continue
        GLOBAL_CACHE.ShMem.SendMessage(
            sender_email,
            account.AccountEmail,
            SharedCommandType.SendDialogToTarget,
            (int(target_id), int(dialog_id), 0, 0),
        )


def _interact_target(target_id: int, call_target: bool = False) -> Generator:
    if target_id <= 0:
        ConsoleLog(BOT_NAME, 'No target to interact with.', Py4GW.Console.MessageType.Warning)
        yield
        return
    Player.ChangeTarget(target_id)
    yield from Routines.Yield.wait(150)
    Player.Interact(target_id, call_target)
    if _send_to_alts:
        _send_to_alts_interact_target(target_id)
    yield


def _interact_npc_xy(x: float, y: float) -> Generator:
    yield from Routines.Yield.Agents.InteractWithAgentXY(x, y, timeout_ms=10000, tolerance=DEFAULT_XY_TOLERANCE)
    target_id = int(Player.GetTargetID() or 0)
    if _send_to_alts and target_id > 0:
        _send_to_alts_interact_target(target_id)
    yield


def _interact_gadget_xy(x: float, y: float) -> Generator:
    yield from Routines.Yield.Agents.InteractWithGadgetXY(x, y, tolerance=DEFAULT_XY_TOLERANCE, timeout_ms=15000)
    target_id = int(Player.GetTargetID() or 0)
    if _send_to_alts and target_id > 0:
        _send_to_alts_interact_target(target_id)
    yield


def _interact_npc_xy_and_dialog(x: float, y: float, dialog_id: int) -> Generator:
    yield from _interact_npc_xy(x, y)
    yield from Routines.Yield.wait(500)
    Player.SendDialog(dialog_id)
    target_id = int(Player.GetTargetID() or 0)
    if _send_to_alts and target_id > 0:
        _send_to_alts_dialog(target_id, dialog_id)
    yield


def _send_dialog_to_current_target(dialog_id: int) -> Generator:
    target_id = int(Player.GetTargetID() or 0)
    if target_id <= 0:
        ConsoleLog(BOT_NAME, 'No current target for dialog.', Py4GW.Console.MessageType.Warning)
        yield
        return
    Player.SendDialog(dialog_id)
    if _send_to_alts:
        _send_to_alts_dialog(target_id, dialog_id)
    ConsoleLog(BOT_NAME, f'Sent dialog {hex(dialog_id)} to target {target_id}')
    yield


def _nearest_from_array(agent_ids: list[int], max_dist: float) -> int:
    filtered = AgentArray.Filter.ByDistance(agent_ids, Player.GetXY(), max_dist)
    sorted_ids = AgentArray.Sort.ByDistance(filtered, Player.GetXY())
    return int(sorted_ids[0]) if len(sorted_ids) > 0 else 0


def _interact_nearest_npc(max_dist: float) -> Generator:
    target_id = _nearest_from_array(AgentArray.GetNPCMinipetArray(), max_dist)
    yield from _interact_target(target_id)


def _interact_nearest_gadget(max_dist: float) -> Generator:
    target_id = _nearest_from_array(AgentArray.GetGadgetArray(), max_dist)
    yield from _interact_target(target_id)


def _interact_fendi_chest(x: Optional[float], y: Optional[float]) -> Generator:
    scan_center = Player.GetXY() if x is None or y is None else (float(x), float(y))
    gadgets = AgentArray.GetGadgetArray()
    gadgets = AgentArray.Filter.ByDistance(gadgets, scan_center, 900.0)
    gadgets = AgentArray.Sort.ByDistance(gadgets, scan_center)
    target_id = 0
    for agent_id in gadgets:
        gadget = Agent.GetGadgetAgentByID(int(agent_id))
        if not gadget:
            continue
        try:
            if int(gadget.gadget_id) == FENDI_CHEST_GADGET_ID:
                target_id = int(agent_id)
                break
        except Exception:
            continue
    if target_id <= 0:
        ConsoleLog(
            BOT_NAME,
            'No Fendi chest found near configured/current position.',
            Py4GW.Console.MessageType.Warning,
        )
        yield
        return
    for _ in range(3):
        yield from _interact_target(target_id)
        yield from Routines.Yield.wait(500)
    yield


def _pickup_torch(max_scan_dist: float = 5000.0, attempts: int = 40) -> Generator:
    inventory = PyInventory.PyInventory()
    me = int(Player.GetAgentID())
    ConsoleLog(BOT_NAME, 'Scanning for torch item')
    for _ in range(attempts):
        items = AgentArray.GetItemArray()
        items = AgentArray.Filter.ByDistance(items, Player.GetXY(), max_scan_dist)
        items = AgentArray.Sort.ByDistance(items, Player.GetXY())
        target_agent = 0
        ground_item_id = 0
        for agent_id in items:
            item_agent = Agent.GetItemAgentByID(int(agent_id))
            if not item_agent:
                continue
            try:
                owner = int(item_agent.owner)
                if owner not in (0, me):
                    continue
            except Exception:
                pass
            try:
                item_id = int(Agent.GetItemAgentItemID(int(agent_id)))
                model_id = int(GLOBAL_CACHE.Item.GetModelID(item_id))
            except Exception:
                continue
            if model_id in TORCH_MODEL_IDS:
                target_agent = int(agent_id)
                ground_item_id = item_id
                break
        if target_agent <= 0:
            yield from Routines.Yield.wait(150)
            continue
        tx, ty = Agent.GetXY(target_agent)
        yield from _move_to_xy(float(tx), float(ty), tolerance=180.0, timeout_ms=9000)
        Player.ChangeTarget(target_agent)
        yield from Routines.Yield.wait(120)
        for _ in range(2):
            try:
                inventory.PickUpItem(target_agent, True)
            except Exception:
                pass
            yield from Routines.Yield.wait(250)
            try:
                inventory.PickUpItem(ground_item_id, True)
            except Exception:
                pass
            yield from Routines.Yield.wait(250)
            try:
                Player.Interact(target_agent, False)
            except Exception:
                pass
            yield from Routines.Yield.wait(450)
            if not Agent.GetItemAgentByID(target_agent):
                ConsoleLog(BOT_NAME, 'Torch picked up')
                yield
                return
    ConsoleLog(BOT_NAME, 'Torch pickup failed', Py4GW.Console.MessageType.Warning)
    yield


def _drop_bundle(times: int = 2, delay_ms: int = 250) -> Generator:
    for _ in range(times):
        yield from Routines.Yield.Keybinds.DropBundle()
        yield from Routines.Yield.wait(delay_ms)
    yield


def _run_interaction(index: int) -> None:
    interaction = INTERACTIONS[index]
    label = interaction['label']
    kind = interaction['kind']
    if kind == 'fendi_chest':
        _queue(label, lambda: _interact_fendi_chest(interaction['x'], interaction['y']))
        return
    if not _xy_ready(interaction):
        _set_status(f'Missing coordinates for: {label}')
        return
    x, y = _parse_xy(interaction)
    if kind == 'npc':
        _queue(label, lambda: _interact_npc_xy(x, y))
    elif kind == 'gadget':
        _queue(label, lambda: _interact_gadget_xy(x, y))
    elif kind == 'npc_dialog':
        dialog_id = int(interaction['dialog_id'] or DWARVEN_BLESSING_DIALOG)
        _queue(label, lambda: _interact_npc_xy_and_dialog(x, y, dialog_id))
    else:
        _set_status(f'Unknown interaction kind for: {label}')


def _log_position() -> None:
    x, y = Player.GetXY()
    target_id = int(Player.GetTargetID() or 0)
    ConsoleLog(BOT_NAME, f'Map={Map.GetMapID()} XY=({x:.2f}, {y:.2f}) target={target_id}')
    _set_status(f'Logged map/position: {Map.GetMapID()} ({x:.0f}, {y:.0f})')


def _draw_interaction_list() -> None:
    global _selected_interaction
    PyImGui.text('Configured interaction buttons')
    for index, interaction in enumerate(INTERACTIONS):
        marker = 'OK' if _xy_ready(interaction) or interaction['kind'] == 'fendi_chest' else 'MISSING XY'
        if PyImGui.button(f'{interaction["label"]} [{marker}]##interaction_{index}'):
            _selected_interaction = index
            _run_interaction(index)


def _draw_selected_editor() -> None:
    global _selected_interaction
    if _selected_interaction < 0 or _selected_interaction >= len(INTERACTIONS):
        _selected_interaction = 0
    interaction = INTERACTIONS[_selected_interaction]
    PyImGui.separator()
    PyImGui.text(f'Selected: {interaction["label"]}')
    PyImGui.text(f'Kind: {interaction["kind"]}')
    if interaction['x'] is None or interaction['y'] is None:
        PyImGui.text('Coordinates: missing in boilerplate')
    else:
        PyImGui.text(f'Coordinates: ({interaction["x"]:.2f}, {interaction["y"]:.2f})')
    if PyImGui.button('Use current player XY for selected'):
        x, y = Player.GetXY()
        interaction['x'] = float(x)
        interaction['y'] = float(y)
        _set_status(f'Set {interaction["label"]} to ({x:.2f}, {y:.2f}) for this session')
    if PyImGui.button('Run selected'):
        _run_interaction(_selected_interaction)


def _draw_quick_actions() -> None:
    PyImGui.separator()
    PyImGui.text('Quick actions')
    if PyImGui.button('Log current map / XY / target'):
        _log_position()
    if PyImGui.button('Interact current target'):
        target_id = int(Player.GetTargetID() or 0)
        _queue('Interact current target', lambda: _interact_target(target_id))
    if PyImGui.button('Send Dwarven blessing dialog to current target'):
        _queue('Dwarven blessing dialog', lambda: _send_dialog_to_current_target(DWARVEN_BLESSING_DIALOG))
    if PyImGui.button('Send Shandra take quest dialog to current target'):
        _queue('Shandra take quest dialog', lambda: _send_dialog_to_current_target(SHANDRA_TAKE_DIALOG))
    if PyImGui.button('Send Shandra reward dialog to current target'):
        _queue('Shandra reward dialog', lambda: _send_dialog_to_current_target(SHANDRA_REWARD_DIALOG))
    if PyImGui.button('Pickup nearest torch'):
        _queue('Pickup nearest torch', lambda: _pickup_torch())
    if PyImGui.button('Drop bundle'):
        _queue('Drop bundle', lambda: _drop_bundle())


def _draw_custom_tools() -> None:
    global _custom_x, _custom_y, _custom_dialog_id, _custom_scan_distance
    PyImGui.separator()
    PyImGui.text('Custom test tools')
    _custom_x = PyImGui.input_float('X##soo_custom_x', _custom_x)
    _custom_y = PyImGui.input_float('Y##soo_custom_y', _custom_y)
    _custom_dialog_id = PyImGui.input_int('Dialog ID##soo_custom_dialog', _custom_dialog_id)
    _custom_scan_distance = PyImGui.input_float('Scan distance##soo_scan_distance', _custom_scan_distance)
    if PyImGui.button('Set custom XY from current position'):
        _custom_x, _custom_y = Player.GetXY()
        _set_status(f'Custom XY set to ({_custom_x:.2f}, {_custom_y:.2f})')
    if PyImGui.button('Move + interact NPC at custom XY'):
        _queue('Custom NPC interaction', lambda: _interact_npc_xy(_custom_x, _custom_y))
    if PyImGui.button('Move + interact gadget at custom XY'):
        _queue('Custom gadget interaction', lambda: _interact_gadget_xy(_custom_x, _custom_y))
    if PyImGui.button('Move + interact NPC + send custom dialog'):
        _queue(
            'Custom NPC dialog interaction',
            lambda: _interact_npc_xy_and_dialog(_custom_x, _custom_y, _custom_dialog_id),
        )
    if PyImGui.button('Interact nearest NPC'):
        _queue('Interact nearest NPC', lambda: _interact_nearest_npc(_custom_scan_distance))
    if PyImGui.button('Interact nearest gadget'):
        _queue('Interact nearest gadget', lambda: _interact_nearest_gadget(_custom_scan_distance))
    if PyImGui.button('Send custom dialog to current target'):
        _queue('Custom dialog to target', lambda: _send_dialog_to_current_target(_custom_dialog_id))


def main() -> None:
    global _send_to_alts
    if window.first_run:
        PyImGui.set_next_window_size(*window.window_size)
        PyImGui.set_next_window_pos(*window.window_pos)
        window.first_run = False
    if PyImGui.begin(MODULE_NAME):
        PyImGui.text('Temporary SoO interaction boilerplate')
        PyImGui.text('Fill INTERACTIONS coordinates later, or test live with custom XY/current XY.')
        _send_to_alts = PyImGui.checkbox('Also send target interactions/dialogs to alts', _send_to_alts)
        PyImGui.text(f'Status: {_last_status}')
        _draw_interaction_list()
        _draw_selected_editor()
        _draw_quick_actions()
        _draw_custom_tools()
    PyImGui.end()


if __name__ == '__main__':
    main()
