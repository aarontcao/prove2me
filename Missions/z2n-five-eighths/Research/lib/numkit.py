"""Shared primitives for the scripts in `instruments/`.

Import numkit before numpy, because the BLAS thread variables only take effect at numpy import.
"""
import json
import os
import sys

__version__ = "1.0"

# Set at import time, so the defaults are in place before numpy loads.
_DEFAULT_THREADS = os.environ.get("NUMKIT_THREADS", "1")
for _var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
             "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_var, _DEFAULT_THREADS)


# --------------------------------------------------------------------------
# resource guards
# --------------------------------------------------------------------------

def pin_threads(n=1):
    """Pin every BLAS threading knob to `n`, since OpenBLAS defaults to one thread per core."""
    if "numpy" in sys.modules:
        raise RuntimeError(
            "pin_threads() called after numpy was imported. The BLAS thread "
            "variables are read at numpy import time, so this call would do "
            "nothing and would do it silently. Move `import numkit` above "
            "`import numpy`.")
    for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        os.environ[var] = str(n)


def mem_guard(gb=None):
    """Cap this process's address space at `gb` GB, and return the cap or None if refused.

    An allocation over the cap raises MemoryError in this process.
    Without it, the kernel's OOM killer picks a victim, which may be another process.
    """
    if gb is None:
        gb = float(os.environ.get("NUMKIT_MEM_GB", 8))
    try:
        import resource
        cap = int(float(gb) * 1024 ** 3)
        soft, hard = resource.getrlimit(resource.RLIMIT_AS)
        if hard != resource.RLIM_INFINITY:
            cap = min(cap, hard)
        resource.setrlimit(resource.RLIMIT_AS, (cap, hard))
        return cap / 1024 ** 3
    except Exception:
        return None


# --------------------------------------------------------------------------
# the validation primitives
# --------------------------------------------------------------------------

def two_routes(a, b, tol=1e-9, label="", quiet=False):
    """Compare one quantity computed two ways, and return the residual in a dict.

    It can't tell two derivations from one code path called twice, so record the routes in `ledger.ndjson`.
    """
    try:
        a_f, b_f = float(a), float(b)
        residual = abs(a_f - b_f)
        scale = max(abs(a_f), abs(b_f), 1.0)
        rel = residual / scale
    except (TypeError, ValueError):
        # Values that float() rejects, like tuples or sets, compare by equality.
        residual = 0.0 if a == b else float("inf")
        rel = residual
    ok = residual <= float(tol)
    out = {"ok": ok, "residual": residual, "rel": rel, "tol": float(tol),
           "a": a if isinstance(a, (int, str)) else repr(a),
           "b": b if isinstance(b, (int, str)) else repr(b),
           "label": label}
    if not quiet:
        print(f"two_routes {label or '?'}: "
              f"{'AGREE' if ok else 'DISAGREE'}  "
              f"residual {residual}  tol {tol}")
    return out


def planted(fn, truth, label="", quiet=False, **kwargs):
    """Run `fn(**kwargs)` and check that it recovers the planted answer `truth`.

    A function that ignores its input can match a known answer, but not a freshly planted one.
    """
    got = fn(**kwargs)
    res = two_routes(got, truth, tol=kwargs.pop("tol", 0), label=label or "planted",
                     quiet=True)
    res["planted"] = truth
    res["recovered"] = got
    if not quiet:
        print(f"planted {label or '?'}: "
              f"{'RECOVERED' if res['ok'] else 'MISSED'}  "
              f"planted {truth}, got {got}")
    return res


def emit(obj):
    """Print the verdict as one JSON line with a `numkit` key. Call it last.

    A caller that records verdicts reads only the last stdout line, so other prints can't pass for a verdict.
    """
    payload = dict(obj)
    payload["numkit"] = __version__
    sys.stdout.flush()
    print(json.dumps(payload, ensure_ascii=False, default=str))
    sys.stdout.flush()
    return payload


# --------------------------------------------------------------------------
# output and checkpoints
# --------------------------------------------------------------------------

def table(path, rows, header=None):
    """Write a column-aligned, greppable table to `path` and return its text."""
    rows = [[str(c) for c in r] for r in rows]
    head = [str(h) for h in (header or [])]
    widths = []
    for i in range(max([len(r) for r in rows] + [len(head)] or [0])):
        widths.append(max([len(r[i]) for r in rows if len(r) > i]
                          + ([len(head[i])] if len(head) > i else [0])))
    out = []
    if head:
        out.append("  ".join(h.ljust(widths[i]) for i, h in enumerate(head)))
        out.append("  ".join("-" * w for w in widths))
    for r in rows:
        out.append("  ".join(c.ljust(widths[i]) for i, c in enumerate(r)))
    text = "\n".join(out) + "\n"
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    return text


def checkpoint(path, obj):
    """Write a JSON checkpoint via a temp file and os.replace, so a kill mid-write can't truncate it."""
    tmp = str(path) + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, default=str)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)
    return path


def resume_from(path, default=None):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


# --------------------------------------------------------------------------
# number theory primitives
# --------------------------------------------------------------------------

def primes_upto(n):
    """Every prime at most n, by a plain sieve."""
    if n < 2:
        return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        i += 1
    return [i for i in range(n + 1) if sieve[i]]


def factorize(n):
    """Prime factorization as a dict {p: e}, by trial division, fine to 10^12."""
    out, n = {}, int(n)
    if n <= 1:
        return out
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n):
    """Every positive divisor of n, sorted."""
    out = [1]
    for p, e in factorize(n).items():
        out = [d * p ** k for d in out for k in range(e + 1)]
    return sorted(out)


def v2(n):
    """The 2-adic valuation of n, with v2(0) = -1 so the result is always an int."""
    n = int(n)
    if n == 0:
        return -1
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def layer(x, n):
    """The 2-adic layer of x in Z_{2^n}: v2(x), with 0 in its own top layer n."""
    x = int(x) % (1 << n)
    return n if x == 0 else v2(x)
