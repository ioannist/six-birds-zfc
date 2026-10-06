"""Small stdlib-only helpers for diagnostics artifacts."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable, Mapping, Sequence


SCHEMA_VERSION = "1.0"


def dump_result(path: str | Path, result: Mapping, generator: str) -> None:
    """Write a JSON result with standard provenance fields."""
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(result)
    payload["schema_version"] = SCHEMA_VERSION
    payload["generator"] = generator
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _escape_tex(value: object) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text


def render_tex_table(
    caption: str,
    label: str,
    header: Sequence[str],
    rows: Iterable[Sequence[object]],
) -> str:
    cols = "l" * len(header)
    lines = [
        r"\begin{table}[t]",
        r"\centering",
        r"\small",
        rf"\caption{{{_escape_tex(caption)}}}",
        rf"\label{{{_escape_tex(label)}}}",
        rf"\begin{{tabular}}{{@{{}}{cols}@{{}}}}",
        r"\toprule",
        " & ".join(_escape_tex(x) for x in header) + r" \\",
        r"\midrule",
    ]
    for row in rows:
        lines.append(" & ".join(_escape_tex(x) for x in row) + r" \\")
    lines.extend([r"\bottomrule", r"\end{tabular}", r"\end{table}", ""])
    return "\n".join(lines)


def tex_table(
    path: str | Path,
    caption: str,
    label: str,
    header: Sequence[str],
    rows: Iterable[Sequence[object]],
    append: bool = False,
) -> None:
    """Emit a LaTeX table. Set append=True to append another table to the same file."""
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    table = render_tex_table(caption, label, header, rows)
    mode = "a" if append else "w"
    with target.open(mode, encoding="utf-8") as handle:
        handle.write(table)
