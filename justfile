# Show available commands.
default:
    @just --list

# Compile one solution. Lean compilation alone accepts `sorry`.
build day:
    #!/usr/bin/env bash
    set -euo pipefail
    day={{ quote(day) }}
    if [[ ! "$day" =~ ^(0?[1-9]|1[0-9]|2[0-4])$ ]]; then
        echo "Problem must be 1 through 24" >&2
        exit 2
    fi
    printf -v number '%02d' "$((10#$day))"
    lake build "Solution.Problem${number}"

# Build and check the configured targets for unpermitted axioms.
check day: (build day)
    #!/usr/bin/env bash
    set -euo pipefail
    day={{ quote(day) }}
    printf -v number '%02d' "$((10#$day))"
    config="comparator/Problem${number}.json"
    {
        printf 'import Solution.Problem%s\n' "$number"
        python3 -c '
    import json, sys
    with open(sys.argv[1], encoding="utf-8") as file:
        config = json.load(file)
    for name in config["theorem_names"] + config["definition_names"]:
        print("#print axioms " + name)
    ' "$config"
    } | lake env lean --stdin | python3 -c '
    import json, re, sys
    with open(sys.argv[1], encoding="utf-8") as file:
        config = json.load(file)
    output = sys.stdin.read()
    print(output, end="")
    targets = config["theorem_names"] + config["definition_names"]
    allowed = set(config["permitted_axioms"])
    reported = {}
    for line in output.splitlines():
        with_axioms = re.fullmatch(r"\x27(.+)\x27 depends on axioms: \[(.*)\]", line)
        without_axioms = re.fullmatch(r"\x27(.+)\x27 does not depend on any axioms", line)
        if with_axioms:
            reported[with_axioms.group(1)] = {name.strip() for name in with_axioms.group(2).split(",") if name.strip()}
        elif without_axioms:
            reported[without_axioms.group(1)] = set()
    missing = set(targets) - reported.keys()
    if missing:
        print("Missing axiom reports: " + ", ".join(sorted(missing)), file=sys.stderr)
        sys.exit(1)
    illegal = {name: axioms - allowed for name, axioms in reported.items() if name in targets and axioms - allowed}
    if illegal:
        for name, axioms in illegal.items():
            print(name + " uses unpermitted axioms: " + ", ".join(sorted(axioms)), file=sys.stderr)
        sys.exit(1)
    print("Quick check passed for all configured targets.")
    ' "$config"

# Run full Comparator on one problem (requires its exporter and landrun setup).
comparator day:
    @scripts/check_comparator.sh {{ quote(day) }}

# Run full Comparator on all 24 problems.
comparator-all:
    @scripts/check_comparator.sh all
