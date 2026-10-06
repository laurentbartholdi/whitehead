#!/usr/bin/env python3
"""Audit proof holes and the source-level Challenge/Solution interface."""
from pathlib import Path
import re

def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, 'Unclosed block comment'
    return ''.join(out)

challenge = strip_comments(Path('Challenge.lean').read_text())
statement = strip_comments(Path('RequestProject/Statement.lean').read_text())
solution = strip_comments(Path('Solution.lean').read_text())
normalize = lambda s: re.sub(r'\s+', ' ', s).strip()
prefix = challenge.split('theorem TheoremA', 1)[0]
assert normalize(prefix + 'end Whitehead') == normalize(statement)
ctype = challenge.split('theorem TheoremA', 1)[1].split(':=', 1)[0]
stype = solution.split('theorem TheoremA', 1)[1].split(':=', 1)[0]
assert normalize(ctype) == normalize(stype), 'Theorem statement changed'
files = [Path('Solution.lean'), *sorted(Path('RequestProject').rglob('*.lean'))]
for path in files:
    text = strip_comments(path.read_text())
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', text), path
print(f'PASS: {len(files)} proof files have no holes or added axioms; statement definitions and theorem type match Challenge.')
