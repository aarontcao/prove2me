"""numkit - the primitives every campaign instrument re-types otherwise.

WHY THIS FILE EXISTS
  The zeta campaign's `gram.py` re-typed a prior run's sieve and von Mangoldt
  code almost verbatim. That is wasted turns, and worse, it is a second copy
  that can disagree with the first. One file, imported, ends both problems.

WHY ONE FILE AND NOT A PACKAGE
  A package needs an install step, and an install step goes stale. A campaign
  script reaches this through PYTHONPATH, which `leanck campaign run` and
  `leanck campaign instrument` both set. Nothing to install, nothing to rot.

IMPORT ORDER MATTERS, AND THIS IS THE ONE GOTCHA
  `import numkit` must come BEFORE `import numpy`. The BLAS thread variables
  only take effect at numpy import time, so setting them afterwards does
  nothing and does it silently. numkit sets them at its own import time and
  imports numpy lazily, inside the functions that need it. `pin_threads` raises
  if numpy is already loaded, so the mistake is loud rather than quiet.

THE VERDICT CHANNEL IS THE LAST STDOUT LINE, AND ONLY THAT
  A long numerical run prints a lot. `leanck campaign instrument` reads the
  verdict from the last stdout line and requires it to be a JSON object with a
  `numkit` key. Use `emit()`. Anything else you print is free text that cannot
  be mistaken for a result. This mirrors the rule in docs/lean-verification.md
  that the auditor's verdict never comes from scraping stdout.
"""
import json
import os
import sys

__version__ = "1.0"

# Set at import time, before numpy can be loaded. See the module docstring.
_DEFAULT_THREADS = os.environ.get("NUMKIT_THREADS", "1")
for _var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
             "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_var, _DEFAULT_THREADS)


# --------------------------------------------------------------------------
# resource guards
# --------------------------------------------------------------------------

def pin_threads(n=1):
    """Pin every BLAS threading knob to `n`.

    A PyPI numpy links OpenBLAS with pthreads and defaults to one thread per
    core. Three jobs on this box's eight vCPUs then ask for twenty-four
    threads, with no swap to absorb the thrash. The system numpy links Debian's
    single-threaded reference libblas, so this problem appears the moment a
    job uses a PyPI numpy and not before.
    """
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
    """Cap this process's address space, in GB.

    THE HIGHEST VALUE FOUR LINES IN THIS FILE
      This box has 32 GB and no swap. Without a cap, an allocation that is too
      large takes the whole machine into an OOM kill, and the kernel picks the
      victim. With one, the process that asked for too much raises MemoryError
      and everything else keeps running.

    Returns the cap actually applied, in GB, or None when the platform refuses.
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
    """Cross-check one quantity computed two independent ways.

    THE POINT IS INDEPENDENCE, AND ONLY YOU CAN SUPPLY THAT
      This function compares two numbers. It cannot tell whether they came from
      genuinely different derivations or from the same code called twice. An
      instrument validated against itself is validated against nothing. State
      in the campaign ledger what the two routes actually were.

    Returns a dict, so that every instrument reports a residual the same way.
    """
    try:
        a_f, b_f = float(a), float(b)
        residual = abs(a_f - b_f)
        scale = max(abs(a_f), abs(b_f), 1.0)
        rel = residual / scale
    except (TypeError, ValueError):
        # Exact objects, integers or Fractions: equality is the whole test.
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
    """Run `fn` on an input whose answer is known, and confirm it recovers it.

    THE TEST PEOPLE SKIP, AND THE ONE THAT MATTERS
      An instrument that reproduces a known answer but cannot detect a planted
      signal may be a constant function. The zeta campaign found exactly that
      failure fifty minutes in: the brief's quantity was identically zero in
      every computable range, so there was nothing to fit. A planted-answer
      test catches it before a day is spent.
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
    """Print one JSON object as the LAST stdout line. The verdict channel.

    `leanck campaign instrument` reads this line and nothing else. A stray
    print elsewhere in the run therefore cannot be mistaken for a verdict.
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
    """Write a column-aligned, greppable table. One format everywhere."""
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
    """Write a JSON checkpoint atomically.

    Temp file plus os.replace, so a process killed mid-write leaves either the
    old checkpoint or the new one, never a truncated file. A nine-minute run
    that dies against the ten-minute wall must not lose everything.
    """
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
    """Prime factorisation as a dict {p: e}. Trial division, fine to 10^12."""
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
    """The 2-adic valuation of n. v2(0) is defined here as -1, not infinity,
    because every caller in this tree wants a sortable integer."""
    n = int(n)
    if n == 0:
        return -1
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def layer(x, n):
    """The 2-adic layer of x in Z_{2^n}: v2(x), with 0 in its own top layer.

    The layer decomposition is the structure the z2n bench's whole argument
    runs on, so it lives here rather than being re-derived per instrument.
    """
    x = int(x) % (1 << n)
    return n if x == 0 else v2(x)
