"""Independent reviewer arithmetic/identity audit; never invokes Lean or Comparator.

This corroborates source review. Python results are not formal proof evidence.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

D = Path(__file__).resolve().parents[2]
PACKET = D / "final-review-packets/MF14-v1"
OUT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


snapshot = json.loads((PACKET / "REVIEW-SNAPSHOT.json").read_text())
assert sha(PACKET / "REVIEW-SNAPSHOT.json") == "e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436"
assert all(sha(PACKET / f) == h for f, h in snapshot["files"].items())
assert {str(f.relative_to(PACKET)) for f in PACKET.rglob("*.lean")} == set(snapshot["Lean_sources"])

# Strip nested Lean block comments, line comments, and strings for the token audit.
def code_only(s):
    out, i, depth, quoted = [], 0, 0, False
    while i < len(s):
        if depth:
            if s[i:i+2] == "/-": depth, i = depth + 1, i + 2
            elif s[i:i+2] == "-/": depth, i = depth - 1, i + 2
            else: i += 1
        elif quoted:
            if s[i] == "\\": i += 2
            elif s[i] == '"': quoted, i = False, i + 1
            else: i += 1
        elif s[i:i+2] == "/-": depth, i = 1, i + 2; out.append(" ")
        elif s[i:i+2] == "--":
            j = s.find("\n", i)
            i = len(s) if j == -1 else j
        elif s[i] == '"': quoted, i = True, i + 1; out.append(" ")
        else: out.append(s[i]); i += 1
    assert depth == 0 and not quoted
    return "".join(out)


lean = {f: code_only((PACKET/f).read_text()) for f in snapshot["Lean_sources"]}
bad_tokens = {}
for f, text in lean.items():
    found = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide|native_axiom|implemented_by|extern|ofReduceBool|ofReduceNat)\b", text)
    if found: bad_tokens[f] = found
assert bad_tokens == {"Challenge.lean": ["sorry"] * 25}, bad_tokens
assert not any(re.search(r"^\s*import\s+Challenge\b", s, re.M) for f, s in lean.items() if f != "Challenge.lean")

headers = {}
for qualified in snapshot["contracts"]:
    name = qualified.split(".")[-1]
    pattern = re.compile(r"\b(?:theorem|lemma)\s+" + re.escape(name) + r"\b(.*?)\s*:=\s*by", re.S)
    ch = pattern.findall(lean["Challenge.lean"])
    found = [(f, m) for f, txt in lean.items() if f != "Challenge.lean" for m in pattern.findall(txt)]
    assert len(ch) == 1 and len(found) == 1, (name, len(ch), found)
    norm = lambda x: " ".join(x.split())
    assert norm(ch[0]) == norm(found[0][1]), name
    headers[qualified] = {"implementation_file": found[0][0], "whitespace_normalized_header_sha256": hashlib.sha256(norm(ch[0]).encode()).hexdigest()}

freeze = json.loads((PACKET / "STATEMENT-FREEZE.json").read_text())
semantic_frozen = ["Challenge.lean", "NLA/MF14/Definitions.lean", "NLA/MF14Degree44/Definitions.lean", "NLA/MF14Degree44/Family.lean", "NLA/MF14Degree44/Degeneration.lean", "NUMERICAL_TARGETS.md", "comparator.json", "lean-toolchain"]
assert all(sha(PACKET/f) == freeze["frozen_files_sha256"][f] for f in semantic_frozen)

# Compute all actual directional derivatives through the displayed 45-parameter
# continuation with exact integer dual polynomials, independently of the stored
# derivative columns and inverse. There is no numerical differentiation.
def plus(a, b):
    r = dict(a)
    for k, v in b.items(): r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v}


def times(a, b):
    r = {}
    for i, u in a.items():
        for j, v in b.items(): r[i+j] = r.get(i+j, 0) + u*v
    return {k: v for k, v in r.items() if v}


class Dual:
    def __init__(self, value, derivative=None):
        self.value = value if isinstance(value, dict) else ({0: value} if value else {})
        self.derivative = derivative or {}
    def __add__(self, other):
        if not isinstance(other, Dual): other = Dual(other)
        return Dual(plus(self.value, other.value), plus(self.derivative, other.derivative))
    __radd__ = __add__
    def __mul__(self, other):
        if not isinstance(other, Dual): other = Dual(other)
        return Dual(times(self.value, other.value), plus(times(self.derivative, other.value), times(self.value, other.derivative)))
    __rmul__ = __mul__
    def __pow__(self, n):
        assert n >= 0
        r = Dual(1)
        for _ in range(n): r = r * self
        return r


X = Dual({1: 1})
base = {0, 22, 32, 34, 35, 44}
derivative_columns = []
for direction in range(45):
    t = [Dual(int(j in base), {0: 1} if j == direction else {}) for j in range(45)]
    q, r = X**4 + t[0]*X**3, X**5 + t[1]*X**3
    p = X**12 + sum((t[j+2]*X**k for j, k in enumerate([3, 6, 7, 8, 9, 10, 11])), Dual(0))
    l3, l4, l5 = [X, X**2, q], [X, X**2, q, r], [X, X**2, q, r, p]
    combination = lambda start, v: sum((t[start+j]*x for j, x in enumerate(v)), Dual(0))
    f = (p + combination(9, l4)) * (r + combination(13, l3))
    g = (f + combination(16, l5)) * (r + combination(21, l3))
    l6 = [X, X**2, q, r, p, f]
    h = (g + combination(24, l6)) * (g + combination(30, l6))
    out = combination(36, [Dual(1), X, X**2, q, r, p, f, g, h])
    assert all(k <= 44 for k in out.value) and all(k <= 44 for k in out.derivative)
    derivative_columns.append(out.derivative)

data = (PACKET / "NLA/MF14Degree44/Mod3Lists.lean").read_text()
def literal(name):
    body = re.search(r"\bdef " + name + r"\s*:\s*List \(List ℕ\)\s*:=\s*(.*?)\n\ndef ", data, re.S).group(1)
    return ast.literal_eval(body)


rows, inverse_columns = literal("jacobianRows"), literal("inverseColumns")
assert len(rows) == len(inverse_columns) == 45
assert all(len(v) == 45 for v in rows + inverse_columns)
assert all(isinstance(x, int) and x >= 0 for v in rows + inverse_columns for x in v)
assert all(rows[i][j] == derivative_columns[j].get(i, 0) for i in range(45) for j in range(45))
assert all(sum(rows[i][k] * inverse_columns[j][k] for k in range(45)) % 3 == int(i == j) for i in range(45) for j in range(45))

# Fraction-free exact determinant, used only as independent corroboration.
a, sign, previous = [row[:] for row in rows], 1, 1
for k in range(44):
    if not a[k][k]:
        pivot = next(i for i in range(k+1, 45) if a[i][k])
        a[k], a[pivot] = a[pivot], a[k]
        sign = -sign
    pivot = a[k][k]
    for i in range(k+1, 45):
        for j in range(k+1, 45):
            numerator = a[i][j]*pivot - a[i][k]*a[k][j]
            assert numerator % previous == 0
            a[i][j] = numerator // previous
        a[i][k] = 0
    previous = pivot
determinant = sign * a[44][44]
assert determinant == 256

receipt = json.loads((PACKET / "local-evidence/RECOVERY-087.json").read_text())
commands = {x["module"]: x for x in receipt["commands"]}
proof_files = [f for f in snapshot["Lean_sources"] if f != "Challenge.lean"]
output_checks = []
for f in proof_files:
    module = "MF14Degree44Solution" if f == "Solution.lean" else f[:-5].replace("/", ".")
    row = commands[module]
    assert row["source_sha256"] == snapshot["Lean_sources"][f]
    assert row.get("exit_code") == 0 or row.get("status") == "reused_exact_successful_local_output"
    for rel, expected in row.get("transitive_source_hashes", {}).items():
        assert snapshot["Lean_sources"][rel] == expected
    output = D / "local-lean/.lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    assert sha(output) == row["output_sha256"]
    output_checks.append(module)
aggregate = commands["MF14Degree44Solution"]
assert aggregate["log_sha256"] == sha(PACKET / "local-evidence/AGGREGATE.log")
assert set(json.loads((PACKET / "local-evidence/AXIOMS.json").read_text())) == set(snapshot["contracts"])
assert all(v == ["propext", "Classical.choice", "Quot.sound"] for v in json.loads((PACKET / "local-evidence/AXIOMS.json").read_text()).values())

result = {
    "purpose": "Independent Python arithmetic and source/evidence identity audit; not Lean or Comparator verification",
    "reviewer": "/root/nr04_mf14_final_referee_a",
    "packet_sha256": sha(PACKET / "REVIEW-SNAPSHOT.json"),
    "registered_files_hash_checked": len(snapshot["files"]),
    "lean_files_hash_checked": len(snapshot["Lean_sources"]),
    "semantic_preproof_freeze_files_matched": semantic_frozen,
    "all_contract_headers_match_after_whitespace_normalization": headers,
    "forbidden_token_findings": bad_tokens,
    "actual_circuit_exact_integer_dual_derivative_entries_matched": 2025,
    "inverse_mod3_entries_checked": 2025,
    "integer_determinant_independently_computed": determinant,
    "receipt087_source_matched_current_olean_hashes_checked": output_checks,
    "lean_run_by_reviewer": False,
    "comparator_run_by_reviewer": False,
}
(OUT / "INDEPENDENT-AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k not in ("all_contract_headers_match_after_whitespace_normalization", "receipt087_source_matched_current_olean_hashes_checked", "forbidden_token_findings")}, indent=2))
print("Matched headers:", len(headers), "Source-matched outputs:", len(output_checks))
