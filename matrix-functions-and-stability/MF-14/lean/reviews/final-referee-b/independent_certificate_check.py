"""Referee-owned, non-Lean sanity check; never supplies an assumption to Lean.

Reconstructs the family using integer polynomial dual numbers, then compares
its derivative at the stated point against every table entry and checks the
modulo-three inverse. Also checks the repetitive certificate source shapes.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

D = Path(__file__).resolve().parents[2]
P = D / "final-review-packets/MF14-v1"
S = P / "NLA/MF14Degree44"


def add(p, q):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def mul(p, q):
    out = {}
    for i, a in p.items():
        for j, b in q.items():
            out[i + j] = out.get(i + j, 0) + a * b
    return {k: v for k, v in out.items() if v}


class Dual:
    def __init__(self, value, first=None):
        self.value = value
        self.first = first or {}

    def __add__(self, other):
        return Dual(add(self.value, other.value), add(self.first, other.first))

    def __mul__(self, other):
        return Dual(mul(self.value, other.value),
                    add(mul(self.first, other.value), mul(self.value, other.first)))


def mono(n):
    return Dual({n: 1})


def lin(c, v):
    assert len(c) == len(v)
    result = Dual({})
    for a, p in zip(c, v):
        result = result + a * p
    return result


def family_direction(j):
    theta = [Dual({0: 1} if i in {0, 22, 32, 34, 35, 44} else {},
                  {0: 1} if i == j else {}) for i in range(45)]
    x, x2 = mono(1), mono(2)
    q = mono(4) + theta[0] * mono(3)
    r = mono(5) + theta[1] * mono(3)
    p = mono(12) + lin(theta[2:9], [mono(n) for n in [3, 6, 7, 8, 9, 10, 11]])
    f = (p + lin(theta[9:13], [x, x2, q, r])) * (r + lin(theta[13:16], [x, x2, q]))
    g = (f + lin(theta[16:21], [x, x2, q, r, p])) * (r + lin(theta[21:24], [x, x2, q]))
    v = [x, x2, q, r, p, f]
    h = (g + lin(theta[24:30], v)) * (g + lin(theta[30:36], v))
    return lin(theta[36:45], [mono(0), x, x2, q, r, p, f, g, h])


text = (S / "Mod3Lists.lean").read_text()
rows = ast.literal_eval(re.search(r"def jacobianRows .*? :=\s*(\[.*?\])\s*def inverseColumns", text, re.S)[1])
inverse_columns = ast.literal_eval(re.search(r"def inverseColumns .*? :=\s*(\[.*?\])\s*def jacobianEntryNat", text, re.S)[1])
assert len(rows) == len(inverse_columns) == 45
assert all(len(row) == 45 for row in rows + inverse_columns)
directions = [family_direction(j) for j in range(45)]
for j, jet in enumerate(directions):
    assert all(k <= 44 for k in jet.value)
    assert all(k <= 44 for k in jet.first)
    assert jet.value == directions[0].value
    for i in range(45):
        assert rows[i][j] == jet.first.get(i, 0), (i, j)
for i in range(45):
    for j in range(45):
        assert sum(rows[i][k] * inverse_columns[j][k] for k in range(45)) % 3 == int(i == j), (i, j)

expansion_indices, value_indices, match_indices = [], [], []
for path in sorted(S.glob("Mod3Columns[0-8].lean")):
    text = path.read_text()
    for m in re.finditer(r"theorem column_expansion_(\d+) : integerDerivativeColumns (\d+) = (.*?) := by\s*(.*?)\n\n", text, re.S):
        n, index = int(m[1]), int(m[2])
        assert n == index
        pairs = re.findall(r"C \((\d+) : ℤ\) \* X \^ (\d+)", m[3])
        assert " + ".join(f"C ({a} : ℤ) * X ^ {k}" for a, k in pairs) == m[3]
        expansion = {}
        for a, k in pairs:
            expansion[int(k)] = expansion.get(int(k), 0) + int(a)
        assert expansion == directions[n].first
        assert re.sub(r"\s+", " ", m[4]).strip() == "dsimp [integerDerivativeColumns] norm_num only [map_ofNat, map_one] ring"
        expansion_indices.append(n)
    for m in re.finditer(r"theorem table_column_values_(\d+) : ∀ i : Fin 45,\s*tableIntegerJacobian i (\d+) = (.*?) := by\s*(.*?)\n\n", text, re.S):
        n, index = int(m[1]), int(m[2])
        assert n == index
        pairs = re.findall(r"\(if i.val = (\d+) then \((\d+) : ℤ\) else 0\)", m[3])
        assert " + ".join(f"(if i.val = {k} then ({a} : ℤ) else 0)" for k, a in pairs) == m[3]
        coeffs = {}
        for k, a in pairs:
            coeffs[int(k)] = coeffs.get(int(k), 0) + int(a)
        assert coeffs == directions[n].first
        assert m[4].strip() == "decide +kernel"
        value_indices.append(n)
    for m in re.finditer(r"theorem column_table_match_(\d+) \(i : Fin 45\) :\s*integerJacobian i (\d+) = tableIntegerJacobian i (\d+) := by\s*(.*?)\n\n", text, re.S):
        n = int(m[1])
        assert n == int(m[2]) == int(m[3])
        expected = f"unfold integerJacobian rw [column_expansion_{n}, table_column_values_{n}] simp only [coeff_add, coeff_C_mul_X_pow]"
        assert re.sub(r"\s+", " ", m[4]).strip() == expected
        match_indices.append(n)
for indices in [expansion_indices, value_indices, match_indices]:
    assert sorted(indices) == list(range(45))

row_indices = []
for path in sorted(S.glob("Mod3Rows[0-8].lean")):
    for m in re.finditer(r"theorem natural_inverse_row_(\d+) : ∀ j : Fin 45,\s*productEntryNat (\d+) j % 3 = if \((\d+) : Fin 45\) = j then 1 else 0 := by\s*(.*?)\n\n", path.read_text(), re.S):
        assert int(m[1]) == int(m[2]) == int(m[3])
        assert m[4].strip() == "decide +kernel"
        row_indices.append(int(m[1]))
assert sorted(row_indices) == list(range(45))

seed_indices = []
for path in sorted(S.glob("SeedFirstColumns[0-8].lean")):
    for m in re.finditer(r"theorem seed_first_column_(\d+) :\s*\(familyFirstJet basePoint\).first \((\d+) : Fin 45\) =\s*\(integerDerivativeColumns (\d+)\).map \(Int.castRingHom ℂ\) := by\s*(.*?)\n\n", path.read_text(), re.S):
        n = int(m[1])
        assert n == int(m[2]) == int(m[3])
        expected = "simp [familyFirstJet, continuationFirstBasis, familyFirstQuad, PolyFirstJet.const, PolyFirstJet.coordinate, PolyFirstJet.add, PolyFirstJet.mul, PolyFirstJet.parameterCombination, PolyFirstJet.finsetSum, basePoint, parameterIndex, integerDerivativeColumns, Fin.sum_univ_succ] <;> ring"
        assert re.sub(r"\s+", " ", m[4]).strip() in [expected, expected + " <;> simp"]
        seed_indices.append(n)
assert sorted(seed_indices) == list(range(2, 45))

result = {
    "scope": "Independent referee Python arithmetic and repetitive-source-shape check; not Lean, not Comparator, not proof input",
    "status": "PASS",
    "reconstructed_family_directions": 45,
    "exact_derivative_table_entries_matched": 2025,
    "modulo_three_product_entries_checked": 2025,
    "whole_polynomial_column_expansions_and_table_formulas_checked": 45,
    "kernel_decide_row_source_patterns_checked": 45,
    "seed_whole_polynomial_direction_source_patterns_checked": 43,
    "seed_columns_0_and_1": "Read individually in SeedFirstPilot.lean; excluded from repetitive-source pattern check",
    "high_derivative_coefficients": "Every reconstructed direction has degree at most 44; no truncation needed",
    "source_snapshot_sha256": hashlib.sha256((P / "REVIEW-SNAPSHOT.json").read_bytes()).hexdigest(),
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
print(json.dumps(result, indent=2))
