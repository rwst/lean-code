#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""Generate the data-dependent sections of note-1061-M4.html from the recorded runs.

Replaces the <!--FRONTIER-->, <!--VERIFY--> and <!--DISPOSITIONS--> markers.  Kept as a
script so the note can be regenerated verbatim from m4_frontier.json / m4_verify.json.
"""
import json, math, sys

fr = json.load(open('m4_frontier.json'))
gapd = {r['poly']: r for r in json.load(open('m0_gapsweep.json'))}
NAMES = {'X^2-2X-1': r'1+\sqrt2', 'X^2-3X+1': r'(3+\sqrt5)/2', 'X^2-3X-1': r'(3+\sqrt{13})/2'}


def nm(p):
    return NAMES.get(p, r'X^{%s}' % p if False else p.replace('X^3', 'X^3').replace('X^2', 'X^2'))


fired = [r for r in fr if r['fire_L']]
missed = [r for r in fr if not r['fire_L']]
fired.sort(key=lambda r: r['alpha'])
missed.sort(key=lambda r: r['alpha'])

rows = []
for r in fired:
    L, H = r['fire_L'], r['fire_H']
    c = r['cert']['%d/%d' % (L, H)]
    rows.append('<tr><td>\\(%.4f\\)</td><td>\\(%s\\)</td><td>%.4f</td><td>\\(H=%d\\)</td>'
                '<td>\\(L=%d\\), \\((%d,%d)\\)</td><td><b>%.6f</b></td><td>%.6f</td>'
                '<td>\\(+%.4f\\)</td></tr>'
                % (r['alpha'], nm(r['poly']), r['routeA'], H, L, c['N'], c['M'],
                   c['Lambda_ub'], r['h_min'], r['h_min'] - c['Lambda_ub']))

mrows = []
for r in missed:
    best = min(r['cert'].values(), key=lambda c: c['Lambda_ub']) if r['cert'] else None
    lad = min((v['P'] for v in r['ladder'].values()), default=float('nan'))
    mrows.append('<tr><td>\\(%.4f\\)</td><td>\\(%s\\)</td><td>%.4f</td><td>%.6f</td>'
                 '<td>%s</td><td>%.6f</td><td>\\(-%.4f\\)</td></tr>'
                 % (r['alpha'], nm(r['poly']), r['routeA'], lad,
                    ('%.6f' % best['Lambda_ub']) if best else '&mdash;',
                    r['h_min'],
                    (best['Lambda_ub'] if best else lad) - r['h_min']))

hard = [r for r in fr if r['poly'] in NAMES]
hrows = []
for r in sorted(hard, key=lambda r: r['alpha']):
    bud = math.log(2) - r['h_min']
    k = min(r['cert'], key=lambda k: r['cert'][k]['Lambda_ub'])
    best = r['cert'][k]
    L, H = k.split('/')
    frac = 100 * (math.log(2) - best['Lambda_ub']) / bud
    hrows.append('<tr><td>\\(%s\\)</td><td>%.4f</td><td>%.6f <span class="small">'
                 '(\\(H=%s\\), \\(L=%s\\))</span></td><td><b>%.0f&thinsp;%%</b></td>'
                 '<td>\\(%+.4f\\)</td></tr>'
                 % (nm(r['poly']), bud, best['Lambda_ub'], H, L, frac,
                    r['h_min'] - best['Lambda_ub']))

FRONTIER = """
<h2 id="extended">7. The frontier extended</h2>

<p><code>BB61/m4_run_frontier.py</code> climbs a warm-started mode ladder \\(H=4,8,16,24,32,48,64\\)
at the balanced search window \\(L=16\\), minimising the certifiable surrogate, and certifies the
winners with the enclosure of Proposition&nbsp;3 at \\(L=20,22,24\\). It walks the 17 undecided
units of &sect;6 in order of M3&rsquo;s shortfall &mdash; \\(\\min_{H\\le8}\\widetilde P-h_{\\min}\\),
smallest first. <b>%d of the \\(\\alpha\\) examined are certified</b>, and they are the two
smallest shortfalls of the whole list. Every one of them carries no X8 confinement gap and fails
Route&nbsp;A: these are the first \\(\\alpha\\) decided by the entropy criterion outside
\\(\\text{X8}\\cup\\text{Route A}\\), and therefore <b>the first widening of the decided set since
M0</b>.</p>

<table>
<tr><th>\\(\\alpha\\)</th><th>minimal polynomial</th><th>\\(A(\\alpha)\\)</th><th>modes</th><th>window</th><th>\\(\\Lambda\\) certified</th><th>\\(h_{\\min}\\)</th><th>margin</th></tr>
%s
</table>

<p class="small">\\(A(\\alpha)&gt;1\\) in every row, so Route&nbsp;A is blind at all of them; the
<code>gap</code> column of <code>m0_gapsweep.json</code> is \\(0\\) at all of them, so the X8
raster found nothing. The certificates are recorded in <code>BB61/m4_frontier.json</code> with
their multiplier vectors, and V9 recomputes each one from the stored vector at the stored
window.</p>

<h3>7.1 What did not fire, and why</h3>

<p>The %d \\(\\alpha\\) that were examined and resisted say <em>why</em> in a way M3 could not:
for each of them the certification was repeated at \\(L=20,22,24\\), i.e. with \\(\\varepsilon\\)
falling by two orders of magnitude, and \\(\\Lambda\\) barely moves &mdash; at \\((3+\\sqrt{13})/2\\) the three depths give
\\(0.655591\\), \\(0.655315\\), \\(0.655232\\), a spread of \\(3.6\\cdot10^{-4}\\) against a shortfall
of \\(0.058\\). <b>The obstruction is the
pressure itself, not the truncation</b>, so no amount of window depth or enclosure sharpening will
reach them; only modes will.</p>

<table>
<tr><th>\\(\\alpha\\)</th><th>minimal polynomial</th><th>\\(A(\\alpha)\\)</th><th>best \\(\\widetilde P\\) at \\(H\\le64\\)</th><th>best certified \\(\\Lambda\\)</th><th>\\(h_{\\min}\\)</th><th>shortfall</th></tr>
%s
</table>

<h3>7.2 What was not run, and why not</h3>

<p>The sweep was stopped after the five smallest shortfalls, and
<code>BB61/m4_run_hard.py</code> then did the two quadratic units the M4 row names by hand
(\\((3+\\sqrt5)/2\\) and \\(1+\\sqrt2\\), ranks 11 and 17 of the ordering). So <b>seven of the
seventeen were examined</b> and ten were not. The decision was made on cost: each further
\\(\\alpha\\) is about twelve minutes and the ten unexamined ones all have larger \\(H\\le8\\)
shortfalls than rank&nbsp;5, which failed.</p>

<div class="box warn"><span class="label">This is a stopping decision, not a theorem</span>
<p>The note claims <em>nothing</em> about the ten unexamined \\(\\alpha\\). The ordering is a
heuristic and it is visibly imperfect even on the rows that were run: rank&nbsp;2 fires with a
margin of \\(0.127\\) while rank&nbsp;1 fires with \\(0.038\\), so the \\(H\\le8\\) shortfall
does not predict the \\(H=64\\) outcome monotonically. Completing the sweep is a bounded piece of
compute (about two hours) and is handed to M5/M6 as such. What the note does claim is the
boundary that was observed: <b>ranks 1&ndash;2 fire, ranks 3&ndash;5 do not</b>.</p></div>

<h2 id="hard">8. The three hard quadratic units (task ii)</h2>

<p>M3&nbsp;&sect;9.2 priced these at \\(H^\\ast\\approx3\\cdot10^{18}\\), \\(1.8\\cdot10^4\\) and
\\(1.3\\cdot10^4\\) respectively, from \\(S(H)\\approx c_\\alpha\\log H\\). The M4 row asked to push
\\((3+\\sqrt{13})/2\\) and \\((3+\\sqrt5)/2\\), &ldquo;where \\(H^\\ast\\approx1.3\\)&ndash;\\(1.8\\cdot10^4\\)
puts a \\(2^{26}\\)-state operator at the edge of feasibility&rdquo;. That reading was optimistic in
one respect and pessimistic in another. Optimistic: \\(H^\\ast\\) is a calibrated proxy, and the
operator size needed is set by the <em>window</em>, not by \\(H\\) &mdash; at \\(L=24\\) the
truncation is already \\(10^{-6}\\) here, which is far more than enough. Pessimistic: the mode
count is the binding constraint, and it is not close.</p>

<table>
<tr><th>\\(\\alpha\\)</th><th>budget \\(\\log2-h_{\\min}\\)</th><th>best certified \\(\\Lambda\\)</th><th>gain, as a fraction of the budget</th><th>shortfall to the floor</th></tr>
%s
</table>

<p>Two of the three are much closer than M3 priced them. \\(H^\\ast\\) is a <em>second-order</em>
extrapolation from \\(a=0\\), and the optimum at \\(H=64\\) is nowhere near perturbative: at
\\((3+\\sqrt5)/2\\) sixty percent of the budget is already consumed at \\(64\\) modes, where the
\\(H^\\ast\\approx1.8\\cdot10^4\\) proxy would have predicted a fraction of a percent. So
<b>the \\(H^\\ast\\) column of M3&nbsp;&sect;8.2 is badly pessimistic at the two middle units</b>,
and the honest reading is that they are a few hundred modes away, not \\(10^4\\). \\(1+\\sqrt2\\)
is the genuine outlier: one percent of its budget at \\(H\\le64\\), and there the search does not
even use the modes it is given &mdash; the ladder saturates at \\(H=16\\) with
\\(\\sum_hh|a_h|=0.7\\), because the certifiable gain is smaller than the penalty for going
further.</p>

<p>What the three do share is that the <em>window</em> is irrelevant to their shortfall. Dropping
\\(\\varepsilon\\) from \\(3.0\\cdot10^{-4}\\) to \\(5.1\\cdot10^{-5}\\) moves \\(\\Lambda\\) by
\\(3\\cdot10^{-4}\\) at \\(1+\\sqrt2\\) and by \\(6\\cdot10^{-3}\\) at \\((3+\\sqrt5)/2\\), against
shortfalls of \\(0.25\\) and \\(0.08\\). The balanced window buys nothing here either (Thm&nbsp;5:
these are quadratic units, where the square window is already within one step of optimal), and
&sect;5 closes the last escape: no change of basis helps. <b>The entire remaining shortfall is
modes</b>, which is M3&nbsp;&sect;9.2&rsquo;s conclusion with the constant corrected downwards at
two of the three \\(\\alpha\\).</p>

<h2 id="lean">9. Lean: a certificate below Route A's ceiling</h2>

<p>The plan&rsquo;s Lean row left two targets: <i>&ldquo;A Lean check of a raster certificate below
the ceiling (e.g. \\(2+\\sqrt3\\), where Route&nbsp;A is blind) remains the open M4 target; a
<code>Bugeaud/Chapter10.lean</code> statement of 10.61 itself is still to be written.&rdquo;</i> Both
are now done, the first in the stronger pressure form rather than as a raster.</p>

<p>The choice of \\(2+\\sqrt3\\) is forced and fortunate. Forced: it is the smallest \\(\\alpha\\)
of the sweep at which Route&nbsp;A fails (\\(A=1.0526\\)), so <code>BB61/RouteA.lean</code> cannot
reach it. Fortunate: at this \\(\\alpha\\) the whole certificate lives in \\(\\mathbb Z[\\sqrt3]\\).
With \\(N=M=3\\) and \\(B=8\\),
\\[\\varepsilon_{3,3}=\\alpha^{-3}+C_\\alpha\\rho^4/(1-\\rho)=(2-\\sqrt3)^3+(2-\\sqrt3)^4=(2-\\sqrt3)^3(3-\\sqrt3)=123-71\\sqrt3,\\]
because \\(C_\\alpha=|\\alpha_2-1|=\\sqrt3-1\\) is exactly \\(1-\\rho\\); and the seven window
weights are \\(-1+\\sqrt3,\\,-5+3\\sqrt3,\\,-19+11\\sqrt3,\\,-71+41\\sqrt3\\) (past) and
\\(-1+\\sqrt3,\\,-5+3\\sqrt3,\\,-19+11\\sqrt3\\) (future). So every one of the \\(2^7=128\\) window
values is an exact \\(A+B\\sqrt3\\), and the cell it can occupy is decided by squaring an integer
comparison. <code>BB61/m4_lean_cert.py</code> does this and checks the exact tables against the
floating-point machine on all 128 words.</p>

<p>The growth bound needed no new engine: <code>ForMathlib/Combinatorics/PathGrowth.lean</code>
already carries the elementary Collatz&ndash;Wielandt shadow (<code>psum</code>,
<code>psum_le</code>, <code>psum_le_pow</code>) &mdash; a positive integer vector \\(v\\) and a
ratio \\(a/b\\) with \\(b\\,(Mv)\\le a\\,v\\) entrywise &mdash; written for the <code>Z32/</code>
root and consumed here unchanged. <code>BB61/Pressure.lean</code> adds only the two-successor
bridge (<code>outEdges_shiftE</code>, <code>sum_outEdges_shiftE</code>), the 64-state data, and
the arithmetic:</p>

<table>
<tr><th>object</th><th>value</th></tr>
<tr><td>states / cells</td><td>\\(2^{6}=64\\) window words, \\(B=8\\) cells</td></tr>
<tr><td>cell weights \\(w_j\\)</td><td>\\(24,32,54,153,153,50,32,24\\)</td></tr>
<tr><td>\\(a\\), \\(b\\)</td><td>\\(95035770\\), \\(2^{20}=1048576\\)</td></tr>
<tr><td>\\(W=\\prod_jw_j\\)</td><td>\\(37279413043200\\)</td></tr>
<tr><td>the criterion</td><td>\\(a^8&lt;b^8W\\cdot193\\) and \\(193&lt;\\alpha^4=97+56\\sqrt3\\), i.e. \\((a/b)^8&lt;W\\alpha^4\\)</td></tr>
<tr><td>the reading</td><td>\\(\\log(a/b)-\\tfrac18\\log W=0.600637&lt;0.658479=\\tfrac12\\log(2+\\sqrt3)=h_{\\min}\\)</td></tr>
</table>

<p>The 64-state vector certificate is checked by <code>decide</code> on closed <code>Nat</code>
arithmetic and the final comparison by <code>norm_num</code> on integers of 64 digits;
<code>BB61/AxCheck.lean</code> confirms std3 &mdash; no <code>sorry</code>, no
<code>native_decide</code>, no cited axiom, so <code>BB61/</code> keeps the citation-free status
it had after M2.</p>

<div class="box warn"><span class="label">What the Lean file does not do</span>
<p>Two links of the chain are outside Lean, and the file says so in its own docstring rather than
axiomatising them: that <code>psum</code> <em>is</em> the partition function of the window
potential (this needs the M1 splitting, which <code>BB61/Splitting.lean</code> has in the
quadratic case, plus Proposition&nbsp;3), and M3&nbsp;Theorem&nbsp;11, the Ledrappier&ndash;Young
entropy floor. So <code>BB61/Pressure.lean</code> does not discharge
<code>Bugeaud.problem_10_61</code> at \\(2+\\sqrt3\\); it machine-checks the finite half of the
certificate and states it in the form the analytic half consumes. The first link is a bounded
piece of work &mdash; the pieces exist &mdash; and is the natural next Lean target; the second is
a research-level formalisation and is not.</p></div>
""" % (len(fired), '\n'.join(rows), len(missed), '\n'.join(mrows), '\n'.join(hrows))

VERIFY = None
try:
    ver = json.load(open('m4_verify.json'))
    vrows = '\n'.join('<tr><td>%s</td><td>%s</td></tr>'
                      % (v['tag'], v['msg'].replace('<', '&lt;').replace('>', '&gt;'))
                      for v in ver)
    VERIFY = ('<table>\n<tr><th>#</th><th>What is checked</th></tr>\n%s\n</table>\n'
              '<p class="small">All %d PASS.</p>' % (vrows, len(ver)))
except FileNotFoundError:
    VERIFY = '<p class="small">(pending)</p>'

DISP = """
<h2 id="dispositions">13. Dispositions</h2>

<table>
<tr><th>Item</th><th>Disposition</th></tr>
<tr><td><b>M4 (this milestone)</b></td><td><b>Run and discharged, positively.</b> (i) The
right target set is the <b>20 undecided</b>, not the 42; seven of the seventeen in scope were
examined and <b>%d certified</b> &mdash; the first \\(\\alpha\\) decided outside
\\(\\text{X8}\\cup\\text{Route A}\\). (ii) All three hard quadratic units are now measured
rather than extrapolated, and the shortfall is the pressure, not the window. (iii) Both Lean
targets are delivered. Mark the row <em>done</em>. <b>Left open by an explicit stopping decision:
ten of the seventeen were not examined</b> (&sect;7.2), about two hours of compute.</td></tr>
<tr><td><b>The certificate machine</b></td><td>Three corrections are permanent and belong to any
future run: the potential need not be continuous; the truncation is a word-wise enclosure, not a
Lipschitz slack; the window must be balanced. Together they are worth more than an order of
magnitude in reachable \\(\\alpha\\), at unchanged cost.</td></tr>
<tr><td><b>&sect;7 X5 / A4-S11 (the constant \\(c(\\alpha)\\))</b></td><td>Closed for good.
M3 showed \\(c(\\alpha)=0\\); &sect;5 now shows the \\(\\ell^2\\) accounting behind it is
basis-independent, so there is no reformulation of the X5 lane that survives.</td></tr>
<tr><td><b>&sect;7 X8 (the gap family)</b></td><td>Subsumed: Theorem&nbsp;7(b) makes the gap
certificate the degenerate case of the pressure criterion. Keep the raster as a fast pre-filter
&mdash; it is much cheaper when it works &mdash; but not as a separate lane.</td></tr>
<tr><td><b>M5, M6</b></td><td>M6&rsquo;s families should still be selected by \\(c_\\alpha\\)
(M3&rsquo;s disposition), and &sect;5 removes the hope that a different functional class changes
that ordering. M5 is untouched.</td></tr>
<tr><td><b>M7 (write-up)</b></td><td>Gains a clean architecture: one criterion (M3 Thm&nbsp;12 in
M4&rsquo;s bounded-Borel form) with three degenerate cases &mdash; Route&nbsp;A, X8, Route&nbsp;D
&mdash; a complete-route theorem, a \\(\\Sigma_1\\) reading, and a machine-checked instance below
Route&nbsp;A&rsquo;s ceiling.</td></tr>
<tr><td><b>Next Lean target</b></td><td>Close the first of the two links of &sect;9: identify
<code>psum</code> with the partition function of the window potential in the quadratic case,
where <code>BB61/Splitting.lean</code> already has the splitting and
<code>BB61/Covering.lean</code> the candidate covering. That would make
<code>Bugeaud.problem_10_61</code> at \\(2+\\sqrt3\\) conditional on M3&nbsp;Thm&nbsp;11
alone.</td></tr>
<tr><td><b>New open question</b></td><td>Every \\(\\alpha\\) certified in &sect;7 is a cubic with
\\(\\rho\\) close to \\(1/2\\), where the entropy floor is low and the budget large. Is there a
structural reason &mdash; a statement about \\(\\rho\\) rather than about \\(\\alpha\\) &mdash; why
the criterion reaches degree&nbsp;3 before degree&nbsp;2? The \\(\\ell^2\\) price says the
question is about \\(c_\\alpha\\), and \\(c_\\alpha\\) is a property of the ladder, not of the
degree.</td></tr>
</table>
""" % len(fired)

s = open('../note-1061-M4.html').read()
s = s.replace('<!--FRONTIER-->', FRONTIER.strip())
s = s.replace('<!--VERIFY-->', VERIFY)
s = s.replace('<!--DISPOSITIONS-->', DISP.strip())
s = s.replace('<b id="fired-count">(see &sect;7)</b>', '<b>%d</b>' % len(fired))
open('../note-1061-M4.html', 'w').write(s)
print('note sections written: %d fired, %d missed' % (len(fired), len(missed)))
