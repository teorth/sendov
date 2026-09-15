"""Verify the private quarter-stage acceptance receipts and record exact bytes."""
from pathlib import Path
import hashlib
import json
import re

STAGE = Path(__file__).resolve().parent
ROOT = STAGE.parents[2]
OBJECTS = STAGE / ".lake/paper/objects"
LOGS = STAGE / ".lake/paper/logs"
MODULES = {
    "Sendov.Analytic.CenteredQuarterEndpoint": "endpoint-02",
    "Sendov.Analytic.CenteredQuarterScalar": "scalar-02",
    "Sendov.Analytic.CenteredQuarterActual": "actual-01",
    "Sendov.Analytic.CenteredQuarterAudit": "audit-final",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


owned = []
lemmas = []
for module, tag in MODULES.items():
    rel = Path(*module.split("."))
    source = STAGE / rel.with_suffix(".lean")
    text = source.read_text()
    assert not re.search(r"\b(sorry|admit|native_decide|axiom)\b", text), source
    lemmas += ["Sendov.CenteredQuarter." + x for x in re.findall(r"^(?:lemma|theorem) (\w+)", text, re.M)]
    receipts = []
    for stem in [tag + "-" + module, "kernel-final-" + module + "-kernel"]:
        path = LOGS / (stem + ".json")
        rec = json.loads(path.read_text())
        assert rec["exit_code"] == 0 and rec["module"] == module, path
        receipts.append({"path": str(path.relative_to(STAGE)), "sha256": sha(path), "seconds": rec["seconds"]})
    artifacts = []
    for suffix in [".olean", ".ilean", ".olean.private", ".olean.server"]:
        path = OBJECTS / rel.with_suffix(suffix)
        if path.exists():
            assert not path.is_symlink(), path
            artifacts.append({"path": str(path.relative_to(STAGE)), "sha256": sha(path)})
    assert any(x["path"].endswith(".olean") for x in artifacts)
    owned.append({"module": module, "source": str(source.relative_to(STAGE)), "source_sha256": sha(source), "artifacts": artifacts, "receipts": receipts})

log = LOGS / "audit-final-Sendov.Analytic.CenteredQuarterAudit.log"
audit = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log.read_text())
assert len(audit) == len(lemmas) == 14
assert set(name for name, _ in audit) == set(lemmas)
for name, axioms in audit:
    assert set(axioms.split(", ")) == {"propext", "Classical.choice", "Quot.sound"}, name

# Record exact project-local dependency source and object identities as observed.
# Package authority remains the pinned environment config plus successful kernel replay.
seen = set(MODULES)
pending = list(MODULES)
dependencies = []
while pending:
    module = pending.pop()
    rel = Path(*module.split("."))
    source = (STAGE if module in MODULES else ROOT) / rel.with_suffix(".lean")
    assert source.exists(), source
    for dep in re.findall(r"^import (Sendov\.[\w.]+)", source.read_text(), re.M):
        if dep in seen:
            continue
        seen.add(dep)
        pending.append(dep)
        drel = Path(*dep.split("."))
        dsource = ROOT / drel.with_suffix(".lean")
        dobject = OBJECTS / drel.with_suffix(".olean")
        assert dsource.exists() and dobject.exists(), dep
        dependencies.append({"module": dep, "source": str(dsource), "source_sha256": sha(dsource), "object": str(dobject.resolve()), "object_sha256": sha(dobject)})

result = {
    "status": "PASS",
    "stage": str(STAGE),
    "owned_modules": owned,
    "audited_lemma_count": len(lemmas),
    "axioms": ["propext", "Classical.choice", "Quot.sound"],
    "audit_log": str(log.relative_to(STAGE)),
    "audit_log_sha256": sha(log),
    "baseline_project_dependency_identities": sorted(dependencies, key=lambda x: x["module"]),
    "remaining_input": "Original finite C sum <= explicit chordTail; no desired-budget premise.",
}
output = STAGE / "receipts/acceptance.json"
output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"status": "PASS", "modules": len(owned), "audited_lemmas": len(lemmas), "baseline_dependency_modules": len(dependencies), "receipt": str(output)}, indent=2))
