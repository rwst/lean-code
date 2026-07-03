#!/usr/bin/env python3
"""Strip all comments from Lean 4 source files.

Removes:
  - line comments        --  ... EOL
  - block comments       /- ... -/   (nested)
  - doc block comments   /-- ... -/   and   /-! ... -/
  - module doc comments  /-! ... -/

Respects string literals ("..."), char literals ('x'), and escapes so that
comment markers inside them are left untouched.

Usage:
    strip_lean_comments.py FILE...        # rewrite each file in place
    strip_lean_comments.py --stdout FILE  # print result, don't modify
"""

import sys


def strip_comments(src: str) -> str:
    out = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]

        # string literal
        if c == '"':
            out.append(c)
            i += 1
            while i < n:
                out.append(src[i])
                if src[i] == '\\' and i + 1 < n:
                    out.append(src[i + 1])
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
            continue

        # char literal  'x'  or  '\n'  (not a general apostrophe: Lean idents
        # can end in ', so only treat as char lit when it closes quickly)
        if c == "'":
            # lookahead: '\?.'  or  '.'
            if i + 2 < n and src[i + 1] == '\\':
                j = i + 2
                while j < n and src[j] != "'":
                    j += 1
                if j < n:
                    out.append(src[i:j + 1])
                    i = j + 1
                    continue
            elif i + 2 < n and src[i + 2] == "'":
                out.append(src[i:i + 3])
                i += 3
                continue
            # otherwise it's a prime in an identifier — emit literally
            out.append(c)
            i += 1
            continue

        # line comment
        if c == '-' and i + 1 < n and src[i + 1] == '-':
            j = i + 2
            while j < n and src[j] != '\n':
                j += 1
            i = j  # keep the newline
            continue

        # block comment (nested), including /-- and /-!
        if c == '/' and i + 1 < n and src[i + 1] == '-':
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if src[j] == '/' and j + 1 < n and src[j + 1] == '-':
                    depth += 1
                    j += 2
                elif src[j] == '-' and j + 1 < n and src[j + 1] == '/':
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue

        out.append(c)
        i += 1

    return ''.join(out)


def cleanup(text: str) -> str:
    # strip trailing whitespace and collapse runs of blank lines to one
    lines = [ln.rstrip() for ln in text.split('\n')]
    result = []
    blank = False
    for ln in lines:
        if ln == '':
            if not blank:
                result.append('')
            blank = True
        else:
            result.append(ln)
            blank = False
    # trim leading/trailing blank lines
    while result and result[0] == '':
        result.pop(0)
    while result and result[-1] == '':
        result.pop()
    return '\n'.join(result) + '\n'


def main(argv):
    to_stdout = False
    files = []
    for a in argv:
        if a == '--stdout':
            to_stdout = True
        else:
            files.append(a)

    if not files:
        print(__doc__)
        return 1

    for path in files:
        with open(path, encoding='utf-8') as f:
            src = f.read()
        result = cleanup(strip_comments(src))
        if to_stdout:
            sys.stdout.write(result)
        else:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(result)
            print(f"stripped: {path}")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
