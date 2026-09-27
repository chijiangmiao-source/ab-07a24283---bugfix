"""回归：命题集合相同但后继不同的位置不得合并。

历史缺陷：乘积构造曾把命题标签相同的位置压成同一“代表位置”，于是一处
可从初态进入并无限滞留的待命位置（与“安全待命”同标“已请求”，但后继
不同）被整体丢弃，`G(!request | F granted)` 被误判成立。

本模块覆盖：
- 同标孪生待命：一处放行、一处滞留，初态可达滞留点 —— 必须判违规，
  证据前缀真正进入滞留位置、闭环只在该处重复且不含放行命题；
- 同标但后继不同的两个位置在多种位置/切换录入顺序下结论不变；
- 不可达的孪生滞留点不影响成立结论；
- 真实放行环成立；
- 普通（标签互异）永不放行环违规；
- 同一分支结构中合规与违规无限执行并存时必须判违规。
"""

import itertools
import unittest

from app.checker import check
from app.validation import validate_request

FORMULA = "G(!request | F granted)"
ROOT = "G((!request | Fgranted))"
BODY = "(!request | Fgranted)"


def _twin_payload(locations, switches):
    return {
        "locations": locations,
        "initial": "init",
        "switches": switches,
        "propositions": {
            "init": [],
            "safe": ["request"],
            "stuck": ["request"],
            "grant": ["granted"],
        },
        "formula": FORMULA,
    }


def twin_payload():
    # init 可进入安全待命（终将放行）或滞留待命（自环永不放行）；
    # safe 与 stuck 命题集合完全相同，外出切换完全不同。
    return _twin_payload(
        ["init", "safe", "stuck", "grant"],
        [
            {"id": "to_safe", "source": "init", "target": "safe"},
            {"id": "to_stuck", "source": "init", "target": "stuck"},
            {"id": "release", "source": "safe", "target": "grant"},
            {"id": "back", "source": "grant", "target": "init"},
            {"id": "hold", "source": "stuck", "target": "stuck"},
        ],
    )


def rewalk(payload, violation):
    """独立重放：每步切换真实存在、目的位置吻合、闭环闭合。"""
    edge = {(sw["source"], sw["id"]): sw["target"]
            for sw in payload["switches"]}
    steps = violation["steps"]
    m = violation["loop_start_index"]
    walked = []
    for i, st in enumerate(steps):
        key = (st["location"], st["switch_taken"])
        assert key in edge, f"步骤 {i} 的切换 {key} 不存在"
        nxt = steps[i + 1]["location"] if i + 1 < len(steps) \
            else steps[m]["location"]
        assert edge[key] == nxt, (
            f"步骤 {i} 切换 {st['switch_taken']} 实际到 {edge[key]}，"
            f"证据却到 {nxt}"
        )
        walked.append(st["location"])
    return walked


class TestTwinStandbyLocations(unittest.TestCase):
    def test_stranded_twin_is_violation(self):
        payload = twin_payload()
        r = check(validate_request(payload))
        self.assertFalse(r.holds, "存在可达滞留待命点，公式必须不成立")
        v = r.violation
        self.assertIsNotNone(v)
        self.assertEqual(v["kind"], "lasso")

    def test_prefix_enters_stranded_location(self):
        payload = twin_payload()
        v = check(validate_request(payload)).violation
        m = v["loop_start_index"]
        prefix_locs = [s["location"] for s in v["steps"][:m]]
        # 前缀真实使用 to_stuck 进入滞留位置（而非同标的安全待命）
        prefix_switches = [s["switch_taken"] for s in v["steps"][:m]]
        self.assertEqual(prefix_locs[0], "init")
        self.assertIn("to_stuck", prefix_switches)
        self.assertEqual(v["steps"][m]["location"], "stuck")
        rewalk(payload, v)

    def test_cycle_repeats_at_stranded_location_without_grant(self):
        payload = twin_payload()
        v = check(validate_request(payload)).violation
        m = v["loop_start_index"]
        cycle = v["steps"][m:]
        # 闭环只在滞留位置重复
        self.assertTrue(all(s["location"] == "stuck" for s in cycle))
        self.assertTrue(all(s["switch_taken"] == "hold" for s in cycle))
        # 闭环上绝不出现放行命题
        for s in cycle:
            self.assertNotIn("granted", s["propositions"])
            self.assertEqual(s["propositions"], ["request"])

    def test_stepwise_subformula_truth_is_falsifying(self):
        payload = twin_payload()
        v = check(validate_request(payload)).violation
        m = v["loop_start_index"]
        for s in v["steps"][m:]:
            t = s["subformula_truth"]
            # 逐子式可复算为违规：已请求、永不放行 -> 请求体假 -> 根公式假
            self.assertTrue(t["request"])
            self.assertFalse(t["!request"])
            self.assertFalse(t["granted"])
            self.assertFalse(t["Fgranted"])
            self.assertFalse(t[BODY])
            self.assertFalse(t[ROOT])
            self.assertIs(s["formula_true_here"], False)
            self.assertEqual(s["formula_true_here"], t[ROOT])

    def test_identical_label_set_does_not_change_conclusion(self):
        # 另一处待命位置即使命题集合与滞留点完全相同，也不能改变
        # 这条实际可达执行的结论：safe 可放行，stuck 仍违规
        payload = twin_payload()
        r = check(validate_request(payload))
        v = r.violation
        loop_locs = {s["location"]
                     for s in v["steps"][v["loop_start_index"]:]}
        self.assertEqual(loop_locs, {"stuck"})
        self.assertNotIn("safe", loop_locs)


class TestEntryOrderInvariance(unittest.TestCase):
    def test_location_and_switch_order_permutations(self):
        base = twin_payload()
        base_switches = base["switches"]
        for loc_order in itertools.permutations(base["locations"]):
            for sw_order in (base_switches, list(reversed(base_switches))):
                payload = _twin_payload(list(loc_order), list(sw_order))
                r = check(validate_request(payload))
                self.assertFalse(
                    r.holds,
                    f"位置顺序 {loc_order} 下漏判滞留违规",
                )
                v = r.violation
                cycle = v["steps"][v["loop_start_index"]:]
                self.assertTrue(
                    all(s["location"] == "stuck" for s in cycle)
                )
                self.assertFalse(
                    any("granted" in s["propositions"] for s in cycle)
                )
                rewalk(payload, v)


class TestTwinControlCases(unittest.TestCase):
    def test_unreachable_stranded_twin_keeps_holds(self):
        # 滞留点不可达（无入射切换，自环满足非死端）：所有可达执行均放行
        payload = _twin_payload(
            ["init", "safe", "stuck", "grant"],
            [
                {"id": "to_safe", "source": "init", "target": "safe"},
                {"id": "release", "source": "safe", "target": "grant"},
                {"id": "back", "source": "grant", "target": "init"},
                {"id": "hold", "source": "stuck", "target": "stuck"},
            ],
        )
        self.assertTrue(check(validate_request(payload)).holds)

    def test_both_twins_release_holds(self):
        # 同标两个待命后继不同，但两条无限执行都终将放行
        payload = {
            "locations": ["init", "safe_a", "safe_b", "grant"],
            "initial": "init",
            "switches": [
                {"id": "a", "source": "init", "target": "safe_a"},
                {"id": "b", "source": "init", "target": "safe_b"},
                {"id": "ra", "source": "safe_a", "target": "grant"},
                {"id": "rb", "source": "safe_b", "target": "safe_a"},
                {"id": "back", "source": "grant", "target": "init"},
            ],
            "propositions": {
                "init": [],
                "safe_a": ["request"],
                "safe_b": ["request"],
                "grant": ["request", "granted"],
            },
            "formula": FORMULA,
        }
        self.assertTrue(check(validate_request(payload)).holds)


class TestOrdinaryLoopsAndBranches(unittest.TestCase):
    def test_real_grant_loop_holds(self):
        # 每个 request 位置都在环上终将到达 granted：真实放行环成立
        payload = {
            "locations": ["idle", "req", "grant"],
            "initial": "idle",
            "switches": [
                {"id": "t1", "source": "idle", "target": "req"},
                {"id": "t2", "source": "req", "target": "grant"},
                {"id": "t3", "source": "grant", "target": "idle"},
            ],
            "propositions": {
                "idle": [],
                "req": ["request"],
                "grant": ["request", "granted"],
            },
            "formula": FORMULA,
        }
        self.assertTrue(check(validate_request(payload)).holds)

    def test_plain_never_granted_loop_violates(self):
        # 标签互异的普通永不放行环：ask(request) -> refuse(denied) -> idle；
        # granted 仅在不可达位置 grant 声明（闭世界：命题须先声明）
        payload = {
            "locations": ["idle", "ask", "refuse", "grant"],
            "initial": "idle",
            "switches": [
                {"id": "t1", "source": "idle", "target": "ask"},
                {"id": "t2", "source": "ask", "target": "refuse"},
                {"id": "t3", "source": "refuse", "target": "idle"},
                {"id": "gg", "source": "grant", "target": "grant"},
            ],
            "propositions": {
                "idle": [],
                "ask": ["request"],
                "refuse": ["denied"],
                "grant": ["granted"],
            },
            "formula": FORMULA,
        }
        r = check(validate_request(payload))
        self.assertFalse(r.holds)
        v = r.violation
        cycle = v["steps"][v["loop_start_index"]:]
        self.assertIn("ask", [s["location"] for s in cycle])
        self.assertFalse(any("granted" in s["propositions"]
                            for s in v["steps"]))
        for s in cycle:
            self.assertFalse(s["formula_true_here"])
        rewalk(payload, v)

    def test_compliant_and_violating_infinite_runs_coexist(self):
        # 同一初态分出两条无限执行：good 环真实放行，bad 环永不放行；
        # good/bad 命题集合相同，必须按“每条无限执行”判违规
        payload = {
            "locations": ["init", "good", "bad", "done"],
            "initial": "init",
            "switches": [
                {"id": "go_good", "source": "init", "target": "good"},
                {"id": "go_bad", "source": "init", "target": "bad"},
                {"id": "grant_it", "source": "good", "target": "done"},
                {"id": "clear", "source": "done", "target": "init"},
                {"id": "wallow", "source": "bad", "target": "bad"},
            ],
            "propositions": {
                "init": [],
                "good": ["request"],
                "bad": ["request"],
                "done": ["granted"],
            },
            "formula": FORMULA,
        }
        r = check(validate_request(payload))
        self.assertFalse(r.holds)
        v = r.violation
        cycle = v["steps"][v["loop_start_index"]:]
        self.assertTrue(all(s["location"] == "bad" for s in cycle))
        self.assertFalse(any("granted" in s["propositions"] for s in cycle))
        rewalk(payload, v)


if __name__ == "__main__":
    unittest.main()
