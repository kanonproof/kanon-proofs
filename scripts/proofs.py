#!/usr/bin/env python3
"""KANON proof bank tooling (no dependencies).

  python3 scripts/proofs.py gate      #1 axiom gate: fail on sorry, native_decide, custom axioms
  python3 scripts/proofs.py lock      #2 statement lock: fail if a theorem statement changed
  python3 scripts/proofs.py relock    rewrite the lock after a reviewed statement change
  python3 scripts/proofs.py manifest  #20 proof manifest for reports (JSON on stdout)
"""
import hashlib, json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = sorted((ROOT / "KanonProofs").glob("*.lean"))
LOCK = ROOT / "statements.lock.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"\bsorry\b", r"\bnative_decide\b", r"^\s*axiom\b", r"\bimplemented_by\b", r"@\[extern", r"\badmit\b"]


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def theorems():
    """(qualified name, file, statement text) for every theorem, statement = text up to ':='."""
    out = []
    for f in SRC:
        text = strip_comments(f.read_text())
        ns = []
        for m in re.finditer(r"^(namespace|end)\s+(\S+)|^theorem\s+(\S+)([\s\S]*?):=", text, re.M):
            if m.group(1) == "namespace":
                ns.append(m.group(2))
            elif m.group(1) == "end" and ns and ns[-1] == m.group(2):
                ns.pop()
            elif m.group(3):
                stmt = " ".join((m.group(3) + m.group(4)).split())
                out.append((".".join(ns + [m.group(3)]), f.name, stmt))
    return out


def gate():
    bad = []
    for f in SRC:
        text = strip_comments(f.read_text())
        for pat in FORBIDDEN:
            for m in re.finditer(pat, text, re.M):
                bad.append(f"{f.name}: forbidden `{m.group(0).strip()}`")
    names = [t[0] for t in theorems()]
    probe = ROOT / "AxiomProbe.lean"
    probe.write_text("import KanonProofs\n" + "".join(f"#print axioms {n}\n" for n in names))
    try:
        r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True, text=True)
    finally:
        probe.unlink()
    if r.returncode != 0:
        print(r.stdout, r.stderr)
        sys.exit("axiom probe failed to run")
    # Lean prints one block per theorem: "'X' depends on axioms: [a, b]" or "'X' does not depend on any axioms".
    seen = 0
    for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", r.stdout):
        seen += 1
        used = {a.strip() for a in (m.group(3) or "").split(",") if a.strip()}
        extra = used - ALLOWED_AXIOMS
        if extra:
            bad.append(f"{m.group(1)} uses axioms {sorted(extra)}")
    if seen != len(names):
        bad.append(f"checked {seen} theorems but found {len(names)} in the sources")
    if bad:
        print("\n".join(bad))
        sys.exit("AXIOM GATE FAILED")
    print(f"axiom gate: {len(names)} theorems, only standard axioms ({', '.join(sorted(ALLOWED_AXIOMS))})")


def digest(stmt):
    return hashlib.sha256(stmt.encode()).hexdigest()[:16]


def current():
    return {n: {"file": f, "sha": digest(s)} for n, f, s in theorems()}


def lock():
    if not LOCK.exists():
        sys.exit("statements.lock.json is missing: run relock after review")
    locked = json.loads(LOCK.read_text())["theorems"]
    now = current()
    changed = [n for n in now if n in locked and locked[n]["sha"] != now[n]["sha"]]
    added = [n for n in now if n not in locked]
    removed = [n for n in locked if n not in now]
    for n in changed: print(f"CHANGED statement: {n}")
    for n in added: print(f"NEW theorem, not reviewed: {n}")
    for n in removed: print(f"REMOVED theorem: {n}")
    if changed or added or removed:
        sys.exit("STATEMENT LOCK FAILED: a reviewer must check the statements against the official source, then run relock")
    print(f"statement lock: {len(now)} statements match their reviewed versions")


def relock(reviewer):
    LOCK.write_text(json.dumps({"reviewedBy": reviewer, "theorems": current()}, indent=2, sort_keys=True) + "\n")
    print(f"locked {len(current())} statements, reviewed by {reviewer}")


def manifest():
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    bank = hashlib.sha256("".join(f"{n}:{v['sha']};" for n, v in sorted(current().items())).encode()).hexdigest()
    print(json.dumps({"repo": "https://github.com/kanonproof/kanon-proofs", "commit": commit, "proofBankHash": bank,
                      "check": "lake build && python3 scripts/proofs.py gate", "theorems": sorted(current())}, indent=2))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "gate": gate()
    elif cmd == "lock": lock()
    elif cmd == "relock": relock(sys.argv[2] if len(sys.argv) > 2 else sys.exit("relock needs a reviewer name"))
    elif cmd == "manifest": manifest()
    else: sys.exit(__doc__)
