"""Tests for numkit. Run with:

    python3 -m pytest lib/ -q

Nothing else in the Lean tree has a test runner, so this file is also the
statement that a campaign primitive is code and gets tested like code. An
instrument built on an untested sieve is not validated, whatever its ledger
event says.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import numkit  # noqa: E402


def test_primes_upto_known():
    assert numkit.primes_upto(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert numkit.primes_upto(1) == []
    assert len(numkit.primes_upto(10 ** 5)) == 9592  # pi(10^5), a known value


def test_factorize_and_divisors():
    assert numkit.factorize(360) == {2: 3, 3: 2, 5: 1}
    assert numkit.divisors(28) == [1, 2, 4, 7, 14, 28]
    assert numkit.factorize(1) == {}
    # A prime squared, where a trial-division loop that stops one step early
    # would silently return the wrong answer.
    assert numkit.factorize(9973 ** 2) == {9973: 2}


def test_v2_and_layer():
    assert [numkit.v2(k) for k in (1, 2, 4, 6, 8, 12)] == [0, 1, 2, 1, 3, 2]
    assert numkit.v2(0) == -1
    # 0 sits in its own top layer, which is the convention the z2n argument uses.
    assert numkit.layer(0, 5) == 5
    assert numkit.layer(16, 5) == 4
    assert numkit.layer(3, 5) == 0


def test_two_routes_agrees_and_disagrees():
    assert numkit.two_routes(1.0, 1.0 + 1e-12, tol=1e-9, quiet=True)["ok"]
    assert not numkit.two_routes(1.0, 1.5, tol=1e-9, quiet=True)["ok"]
    # Exact objects fall through to equality, which is the whole test there.
    assert numkit.two_routes(40, 40, tol=0, quiet=True)["ok"]
    assert not numkit.two_routes(40, 41, tol=0, quiet=True)["ok"]


def test_planted_detects_and_misses():
    good = numkit.planted(lambda: 25, truth=25, quiet=True)
    assert good["ok"] and good["recovered"] == 25
    # A constant function is exactly the failure planted() exists to catch.
    bad = numkit.planted(lambda: 0, truth=25, quiet=True)
    assert not bad["ok"]


def test_pin_threads_raises_after_numpy(tmp_path):
    """The silent-failure guard. Setting the BLAS variables after numpy loads
    does nothing, so numkit must refuse rather than pretend."""
    script = tmp_path / "late.py"
    script.write_text(
        "import sys; sys.path.insert(0, %r)\n"
        "import numpy\n"
        "import numkit\n"
        "try:\n"
        "    numkit.pin_threads(4)\n"
        "    print('NO RAISE')\n"
        "except RuntimeError:\n"
        "    print('RAISED')\n" % str(Path(numkit.__file__).parent))
    out = subprocess.run([sys.executable, str(script)], capture_output=True,
                         text=True)
    assert "RAISED" in out.stdout, out.stdout + out.stderr


def test_checkpoint_is_atomic_and_round_trips(tmp_path):
    p = tmp_path / "ck.json"
    numkit.checkpoint(p, {"n": 7, "found": [1, 2, 3]})
    assert numkit.resume_from(p) == {"n": 7, "found": [1, 2, 3]}
    assert not (tmp_path / "ck.json.tmp").exists()
    assert numkit.resume_from(tmp_path / "nope.json", default={}) == {}
    # A truncated checkpoint reads as absent, not as a crash.
    p.write_text('{"n": 7, "fou')
    assert numkit.resume_from(p, default="fallback") == "fallback"


def test_emit_is_the_last_stdout_line(tmp_path, capsys):
    print("chatter that must not be read as a verdict")
    numkit.emit({"ok": True, "residual": 0})
    lines = [ln for ln in capsys.readouterr().out.splitlines() if ln.strip()]
    payload = json.loads(lines[-1])
    assert payload["ok"] is True and payload["numkit"] == numkit.__version__


def test_table_is_aligned(tmp_path):
    p = tmp_path / "t.txt"
    numkit.table(p, [[1, 1], [2, 2], [7, 80]], header=["n", "f(n)"])
    text = p.read_text()
    assert "n  f(n)" in text
    assert "7  80" in text
