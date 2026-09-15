#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Splice the data tables of note-1061-M7.html from the recorded JSON.

Idempotent: each region of the note is delimited by <!--TAG--> ... <!--/TAG--> and is
rewritten in place from BB61/m7_*.json, so the note never disagrees with the runs.
Regions: PRICE (the E_H bracket), SWEEP (the completed frontier), LADDER (the memory
ladder of the ladder limits), ALPHA2 (the degeneration at alpha = 2), VERIFY.
"""
import json, re, math, sys

NOTE = '/home/ralf/math/lean-code/note-1061-M7.html'
NAMES = {'1+sqrt2': r'\(1+\sqrt2\)', '(3+sqrt5)/2': r'\((3+\sqrt5)/2\)',
         '(3+sqrt13)/2': r'\((3+\sqrt{13})/2\)', '2+sqrt3': r'\(2+\sqrt3\)'}


def tex(p):
    """X^10-2X^9-1 -> X^{10}-2X^{9}-1, so MathJax does not eat the second digit."""
    return re.sub(r'\^(\d+)', lambda m: '^{%s}' % m.group(1), p)


def nm(p):
    return NAMES.get(p, r'\(%s\)' % tex(p))


def price():
    rows = json.load(open('m7_price.json'))
    out = ['<table><tr><th>\\(\\alpha\\)</th><th>\\(h_{\\min}\\)</th><th>\\(H\\)</th>'
           '<th>\\(E_H\\) upper (optimiser)</th><th>\\(E_H\\) lower (explicit mixture)</th>'
           '<th>atoms</th><th>verdict</th></tr>']
    for r in rows:
        ks = sorted(r['rows'], key=int)
        for i, k in enumerate(ks):
            v = r['rows'][k]
            lb = ('%.6f' % v['E_lb']) if v['E_lb'] is not None else '&mdash;'
            vd = ('no certificate of degree \\(\\le %s\\)' % k) if v['no_cert'] else \
                 ('pool too small' if v['E_lb'] is None else 'inconclusive')
            out.append('<tr>%s%s<td>%s</td><td>%.6f</td><td>%s</td><td>%d</td><td>%s</td></tr>'
                       % ('<td rowspan="%d">%s</td>' % (len(ks), nm(r['poly'])) if i == 0 else '',
                          '<td rowspan="%d">%.4f</td>' % (len(ks), r['h_min']) if i == 0 else '',
                          k, v['E_ub'], lb, v['atoms'], vd))
    out.append('</table>')
    return '\n'.join(out)


def sweep():
    old = json.load(open('m4_frontier.json'))
    new = json.load(open('m7_frontier.json'))
    out = ['<table><tr><th>\\(\\alpha\\)</th><th>minimal polynomial</th><th>\\(A(\\alpha)\\)</th>'
           '<th>\\(h_{\\min}\\)</th><th>best \\(\\widetilde P\\), \\(H\\le64\\)</th>'
           '<th>shortfall</th><th>run</th></tr>']
    rows = [(r, 'M4') for r in old] + [(r, 'M7') for r in new]
    rows.sort(key=lambda t: min(v['P'] for v in t[0]['ladder'].values()) - t[0]['h_min'])
    for r, who in rows:
        P = min(v['P'] for v in r['ladder'].values())
        fired = r['fire_L'] is not None
        out.append('<tr><td>%.4f</td><td>\\(%s\\)</td><td>%.3f</td><td>%.4f</td><td>%s</td>'
                   '<td>%s</td><td>%s</td></tr>'
                   % (r['alpha'], tex(r['poly']), r['routeA'], r['h_min'],
                      ('<b>%.6f</b>' % P) if fired else '%.6f' % P,
                      ('<b>fires, margin +%.4f</b>' % (r['h_min'] - r['cert']['%d/%d'
                       % (r['fire_L'], r['fire_H'])]['Lambda_ub'])) if fired
                      else '%.4f' % (r['h_min'] - P), who))
    out.append('</table>')
    return '\n'.join(out)


def ladder():
    rows = json.load(open('m7_ladder.json'))
    Ns = []
    for r in rows:
        for k in r['rows']:
            Ns = sorted({int(n) for n in r['rows'][k] if n != 'bern'})
    out = ['<table><tr><th>\\(\\alpha\\)</th><th>memory \\(k\\)</th><th>parameters</th>'
           + ''.join('<th>%d ladders</th>' % n for n in Ns)
           + '<th>Bernoulli</th></tr>']
    for r in rows:
        ks = sorted(r['rows'], key=int)
        for i, k in enumerate(ks):
            v = r['rows'][k]
            out.append('<tr>%s<td>%s</td><td>%d</td>%s<td>%.6f</td></tr>'
                       % ('<td rowspan="%d">%s</td>' % (len(ks), nm(r['poly'])) if i == 0 else '',
                          k, 1 << int(k),
                          ''.join('<td>%s</td>' % (('%.6f' % v[str(n)]['min_max_L'])
                                                   if str(n) in v else '&mdash;') for n in Ns),
                          v['bern']))
    out.append('</table>')
    return '\n'.join(out)


def alpha2():
    rows = json.load(open('m7_alpha2.json'))
    fam = [r for r in rows if r['poly'].endswith('-1') and r['poly'].count('X') == 2
           and r['d'] >= 2]
    out = ['<table><tr><th>minimal polynomial</th><th>\\(d\\)</th><th>\\(\\alpha\\)</th>'
           '<th>\\(\\rho\\)</th><th>\\(h_{\\min}\\)</th><th>budget \\(\\log2-h_{\\min}\\)</th>'
           '<th>\\(\\sup_{h\\le4096}|\\Phi_h|\\)</th><th>\\(S(4096)\\)</th>'
           '<th>budget\\(/S\\)</th></tr>']
    seen = set()
    for r in rows:
        if r['poly'] in seen:
            continue
        seen.add(r['poly'])
        out.append('<tr><td>\\(%s\\)</td><td>%d</td><td>%.7f</td><td>%.4f</td><td>%.5f</td>'
                   '<td>%.5f</td><td>%.2e</td><td>%.2e</td><td>%.2e</td></tr>'
                   % (tex(r['poly']), r['d'], r['alpha'], r['rho'], r['h_min'], r['budget'],
                      r['sup'], r['S'], r['ratio']))
    out.append('</table>')
    return '\n'.join(out)


def verify():
    rows = json.load(open('m7_verify.json'))
    out = ['<table><tr><th>id</th><th>checks</th><th>result</th></tr>']
    for r in rows:
        out.append('<tr><td>%s</td><td>%s</td><td>%s &mdash; %s</td></tr>'
                   % (r['id'], r['what'], 'PASS' if r['ok'] else '<b>FAIL</b>', r['detail']))
    out.append('</table>')
    n = sum(1 for r in rows if r['ok'])
    out.append('<p class="small">%d/%d PASS.</p>' % (n, len(rows)))
    return '\n'.join(out)


BUILD = dict(PRICE=price, SWEEP=sweep, LADDER=ladder, ALPHA2=alpha2, VERIFY=verify)

if __name__ == '__main__':
    s = open(NOTE).read()
    for tag, fn in BUILD.items():
        if '<!--%s-->' % tag not in s:
            continue
        try:
            body = fn()
        except Exception as e:
            print('  %-7s skipped (%s)' % (tag, e))
            continue
        s = re.sub(r'<!--%s-->.*?<!--/%s-->' % (tag, tag),
                   lambda m: '<!--%s-->\n%s\n<!--/%s-->' % (tag, body, tag), s, flags=re.S)
        print('  %-7s spliced (%d chars)' % (tag, len(body)))
    open(NOTE, 'w').write(s)
    print('-> %s' % NOTE)
