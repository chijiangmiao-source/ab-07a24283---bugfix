#!/usr/bin/env python3
"""Compose verify 服务入口：

1. 构建检查：全部源码可编译（字节码语法检查）；
2. 代码测试：unittest 全量用例（含永不放行违规闭环检测）；
3. HTTP 冒烟：健康检查、成立结论、违规闭环证据、非法请求 400 且无审计、编号读取。

任一步失败即以非零退出码退出。
"""
import json
import os
import py_compile
import sys
import unittest
import urllib.error
import urllib.request

BASE = os.environ.get("LTL_BASE_URL", "http://ltl:8080")
FAILURES = []


def section(title):
    print(f"\n=== {title} ===", flush=True)


def check(name, cond, detail=""):
    mark = "PASS" if cond else "FAIL"
    print(f"[{mark}] {name}{(' — ' + detail) if detail and not cond else ''}",
          flush=True)
    if not cond:
        FAILURES.append(name)


def http(method, path, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(BASE + path, data=data, headers=headers,
                                 method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


# 永不放行（饥饿）闭环：request 出现后可不经 granted 直接返回
STARVATION = {
    "locations": ["idle", "req", "deny", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "deny"},
        {"id": "t4", "source": "deny", "target": "idle"},
        {"id": "tg", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "deny": ["denied"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

COMPLIANT = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "grant"},
        {"id": "t3", "source": "grant", "target": "idle"},
    ],
    "propositions": {"idle": [], "req": ["request"],
                     "grant": ["request", "granted"]},
    "formula": "G(!request | F granted)",
}

# 两处同命题（request）待命位置：wait_safe 安全待命会进入放行位置，
# wait_stuck 滞留待命从初态可达并可无限停留（t_stay 自闭环）。
# 正确结论必须是 holds=false：idle -t_req_stuck-> wait_stuck -t_stay↺
TWO_STANDBY = {
    "locations": ["idle", "wait_safe", "wait_stuck", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t_req_safe",  "source": "idle",       "target": "wait_safe"},
        {"id": "t_req_stuck", "source": "idle",       "target": "wait_stuck"},
        {"id": "t_stay",      "source": "wait_stuck", "target": "wait_stuck"},
        {"id": "t_permit",    "source": "wait_safe",  "target": "grant"},
        {"id": "t_clear",     "source": "grant",      "target": "idle"},
    ],
    "propositions": {
        "idle":       [],
        "wait_safe":  ["request"],
        "wait_stuck": ["request"],
        "grant":      ["request", "granted"],
    },
    "formula": "G(!request | F granted)",
}


def main():
    # 1. 构建检查
    section("构建检查 py_compile")
    compile_ok = True
    app_dir = os.path.join(os.path.dirname(__file__), "..", "app")
    for name in sorted(os.listdir(app_dir)):
        if name.endswith(".py"):
            path = os.path.join(app_dir, name)
            try:
                py_compile.compile(path, doraise=True)
                print(f"[PASS] compile {name}", flush=True)
            except py_compile.PyCompileError as exc:
                compile_ok = False
                print(f"[FAIL] compile {name}: {exc}", flush=True)
    check("全部源码编译通过", compile_ok)

    # 2. 代码测试
    section("代码测试 unittest")
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    sys.path.insert(0, root)
    loader = unittest.TestLoader()
    suite = loader.discover(os.path.join(root, "tests"), top_level_dir=root)
    runner = unittest.TextTestRunner(verbosity=1)
    result = runner.run(suite)
    check("单元测试全部通过", result.wasSuccessful(),
          f"{len(result.failures)+len(result.errors)} 个失败")

    # 3. HTTP 冒烟
    section("HTTP 冒烟")
    status, body = http("GET", "/health")
    check("GET /health 200 ok", status == 200 and body.get("status") == "ok",
          f"status={status}")

    status, body = http("POST", "/checks", COMPLIANT)
    ok_id = body.get("id")
    check("合规规程 POST /checks 201 且 holds=true",
          status == 201 and body.get("holds") is True and ok_id,
          f"status={status} body={body}")

    status, body = http("GET", f"/checks/{ok_id}")
    check("按编号读取成立结论",
          status == 200 and body.get("id") == ok_id
          and body.get("holds") is True,
          f"status={status}")
    check("记录含否定 NNF 与自动机方法说明",
          "negation_nnf" in body.get("normalization", {}),
          str(body.get("normalization")))

    status, body = http("POST", "/checks", STARVATION)
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    loop_locs = [s.get("location") for s in steps[m:]] if m is not None else []
    loop_false = all(s.get("formula_true_here") is False
                     for s in steps[m:]) if m is not None else False
    evidence_ok = all(
        isinstance(s.get("subformula_truth"), dict)
        and s.get("switch_taken") for s in steps
    )
    check("永不放行违规闭环 POST 201 且 holds=false",
          status == 201 and body.get("holds") is False and v,
          f"status={status}")
    check("闭环经过 request 且不经过 granted",
          "req" in loop_locs and "grant" not in loop_locs,
          f"loop_locs={loop_locs}")
    check("闭环上公式逐点为假（无限违规，非有限回放）", loop_false)
    check("每步含位置/切换/子式真值证据", evidence_ok)
    check("违规同样保存并可按编号读取",
          body.get("id") and http("GET", f"/checks/{body['id']}")[0] == 200)

    # ---- 同命题双待命位置场景：滞留待命闭环必须被判违规 ----
    section("HTTP 场景：同命题双待命（安全/滞留）")
    from app.ltl_parser import parse_formula
    declared = set()
    for plist in TWO_STANDBY["propositions"].values():
        declared.update(plist)
    root_key = parse_formula(TWO_STANDBY["formula"], declared).to_str()

    status, body = http("POST", "/checks", TWO_STANDBY)
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    prefix = steps[:m] if m is not None else []
    loop = steps[m:] if m is not None else []
    check("同命题双待命规程 POST 201 且 holds=false",
          status == 201 and body.get("holds") is False and v,
          f"status={status} holds={body.get('holds')}")
    check("前缀自初态 idle 经 t_req_stuck 进入滞留待命 wait_stuck",
          bool(prefix) and prefix[0].get("location") == "idle"
          and prefix[-1].get("switch_taken") == "t_req_stuck"
          and bool(loop) and loop[0].get("location") == "wait_stuck",
          f"prefix={[s.get('location') for s in prefix]}")
    check("闭环只含 wait_stuck 且反复执行其闭环切换 t_stay",
          bool(loop)
          and all(s.get("location") == "wait_stuck" for s in loop)
          and {s.get("switch_taken") for s in loop} == {"t_stay"},
          f"loop={[(s.get('location'), s.get('switch_taken')) for s in loop]}")
    check("闭环逐步命题含 request 且从不出现 granted",
          bool(loop) and all(
              "request" in s.get("propositions", [])
              and "granted" not in s.get("propositions", [])
              for s in loop))
    check("闭环上根公式与 Fgranted 逐步为假、request 为真（可复算违规）",
          bool(loop) and all(
              s.get("formula_true_here") is False
              and s.get("subformula_truth", {}).get(root_key) is False
              and s.get("subformula_truth", {}).get("Fgranted") is False
              and s.get("subformula_truth", {}).get("request") is True
              for s in loop))
    check("违规证据可按编号读取",
          body.get("id") and http("GET", f"/checks/{body['id']}")[0] == 200)

    # 位置/切换录入顺序变化：结论与闭环位置不变
    perm = json.loads(json.dumps(TWO_STANDBY))
    perm["locations"] = list(reversed(perm["locations"]))
    perm["switches"] = list(reversed(perm["switches"]))
    status, body2 = http("POST", "/checks", perm)
    v2 = body2.get("violation") or {}
    steps2 = v2.get("steps", [])
    m2 = v2.get("loop_start_index")
    loop2 = steps2[m2:] if m2 is not None else []
    check("录入顺序变化后结论仍为不成立且闭环仍在 wait_stuck",
          status == 201 and body2.get("holds") is False
          and bool(loop2)
          and all(s.get("location") == "wait_stuck" for s in loop2),
          f"status={status} holds={body2.get('holds')}")

    bad = json.loads(json.dumps(STARVATION))
    bad["switches"] = bad["switches"][:2]  # deny/grant 变死端
    status, body = http("POST", "/checks", bad)
    check("死端请求 400 且不分配编号",
          status == 400 and "id" not in body
          and any("死端" in e for e in body.get("errors", [])),
          f"status={status} body={body}")

    bad2 = json.loads(json.dumps(COMPLIANT))
    bad2["switches"][0]["target"] = "ghost"
    status, body = http("POST", "/checks", bad2)
    check("悬空端点 400 定位拒绝",
          status == 400 and any("悬空端点" in e for e in body.get("errors", [])))

    bad3 = json.loads(json.dumps(COMPLIANT))
    bad3["formula"] = "request U granted"
    status, body = http("POST", "/checks", bad3)
    check("非法公式 400 定位拒绝", status == 400)

    status, body = http("GET", "/checks/CHK-000000")
    check("不存在编号 404", status == 404)

    section("汇总")
    if FAILURES:
        print(f"verify 失败 {len(FAILURES)} 项：{FAILURES}", flush=True)
        sys.exit(1)
    print("verify 全部通过，退出码 0", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
