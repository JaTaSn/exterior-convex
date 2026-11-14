# 2026-11-09 - Claude-Code (jts-mini) subagent, for working-notes/hstar-sketches-proofs-2026-11-09.org.
#   Independent cross-check of the codegree theorem on small cases: Koz(n;d) is built as a Minkowski sum of vertex sets
#   in Sage (its own convex hull and H-description), interior lattice points of P and 2P are counted with
#   relative_interior_contains, and compared with the reciprocity counts (INT lines) of hstar_codegree_t2_check.py
#   (2P enumerated only for n = 3 and for r <= 2; elsewhere the two points of sketch 1 are tested in relint(2P)).
#   The two lattice points produced by the proof's construction are checked to be interior the same way.
#   Usage, from the project directory: sage code/oneoff/hstar_codegree_sage_crosscheck.sage
import itertools, re

def koz(n, ds):
    """Koz(n;ds) projected to its free coordinates U = union [d+2, d+n] (the others are constant integers)."""
    N = n + ds[-1]
    U = sorted(set(k for d in ds for k in range(d + 2, d + n + 1)))
    P = None
    for d in ds:
        verts = []
        for j in range(1, n + 1):
            v = [0] * (N + 1)
            for k in range(j + 1):
                v[d + k] = binomial(n, k)
            verts.append([v[k] for k in U])
        S = Polyhedron(vertices=verts, base_ring=QQ)
        P = S if P is None else P + S
    return P, U

def exposed(n, ds):
    r = len(ds)
    return [i for i in range(r) if not (i > 0 and ds[i-1] == ds[i]) and (i == r-1 or ds[i+1] - ds[i] >= n-1)]

def interior_trunc(n, j):
    x = [0] * (n + 1); x[0], x[1], x[j] = 1, n, 1
    for k in range(j - 1, 1, -1):
        x[k] = (binomial(n, k) * x[k+1]) // binomial(n, k+1) + 1
    return x

def interior_2K(n, which):
    x = [0] * (n + 1); x[0], x[1], x[n] = 2, 2 * n, 1
    for k in range(n - 1, 1, -1):
        x[k] = (binomial(n, k) * x[k+1]) // binomial(n, k+1) + 1
    x[2] += which
    return x

def construct(n, ds, which):
    N = n + ds[-1]; x = [0] * (N + 1); s, T, first = len(ds), None, True
    while s > 0:
        top = ds[s-1]
        if T is None or T - top >= n:
            m = sum(1 for d in ds[:s] if d == top)
            if m < 2: return None
            a = interior_2K(n, which if first else 0); a[0] += m - 2; a[1] += (m - 2) * n
            for k in range(n + 1): x[top + k] += a[k]
            s -= m; T = top + 1
        else:
            A = [i for i in range(s) if T - ds[i] <= n - 1]
            for i in A:
                y = interior_trunc(n, T - ds[i])
                for k in range(n + 1): x[ds[i] + k] += y[k]
            k0 = min(A); s, T = k0, ds[k0] + 1
        first = False
    return x

ref = {}
for line in open('runs/2026-11-09_hstar-codegree-t2-check.txt'):
    if line.startswith('INT ') and len(line.split()) == 6 and line.split()[1].isdigit():
        _, n, d, i1, i2, cg = line.split()
        ref[(int(n), tuple(int(a) for a in d.split(',')))] = (int(i1), int(i2), int(cg))
print('# hstar_codegree_sage_crosscheck.sage, 2026-11-09, Claude-Code (jts-mini) subagent;', version(), flush=True)
print('# reference: %d INT lines from runs/2026-11-09_hstar-codegree-t2-check.txt' % len(ref))
cases = []
for n, rmax, dmax in [(3, 4, 4), (4, 3, 4)]:
    for r in range(1, rmax + 1):
        for gaps in itertools.product(range(0, n + 1), repeat=r - 1):
            ds = [0]
            for g in gaps: ds.append(ds[-1] + g)
            if ds[-1] <= dmax: cases.append((n, tuple(ds)))
def sum_of_twoK(n, ds, which):
    """Sketch 1: sum of shift^{d_i} q with q interior in 2Koz(n), the last summand's q varied."""
    N = n + ds[-1]; x = [0] * (N + 1)
    for i, d in enumerate(ds):
        q = interior_2K(n, which if i == len(ds) - 1 else 0)
        for k in range(n + 1): x[d + k] += q[k]
    return x

# Full enumeration of 2P only where it is small (n = 3, or n = 4 with r <= 2); elsewhere codegree 2 is
# certified by int(P) = 0 together with the two points of sketch 1 lying in relint(2P), tested by Sage.
bad = 0
for n, ds in cases:
    P, U = koz(n, list(ds))
    D = P.dim()
    pts = P.integral_points()
    i1 = sum(1 for p in pts if P.relative_interior_contains(p))
    pred = 2 if exposed(n, list(ds)) else 1
    msg = []
    i2 = None
    if i1 > 0:
        codeg = 1
        ok = i1 >= 2
    else:
        P2 = 2 * P
        two = [vector(QQ, [x[k] for k in U]) for x in (sum_of_twoK(n, list(ds), w) for w in (0, 1))]
        ok2 = two[0] != two[1] and all(P2.relative_interior_contains(y) for y in two)
        msg.append('sketch-1 points in relint(2P): %s' % ok2)
        codeg = 2 if ok2 else None
        ok = ok2
        if n == 3 or len(ds) <= 2:
            i2 = sum(1 for p in P2.integral_points() if P2.relative_interior_contains(p))
            ok = ok and i2 >= 2
    ok = ok and codeg == pred
    if (n, ds) in ref:
        r1, r2, rc = ref[(n, ds)]
        agree = r1 == i1 and rc == codeg and (i2 is None or i2 == r2)
        msg.append('reciprocity counts agree' if agree else 'DISAGREE with reciprocity %s' % (ref[(n, ds)],))
        ok = ok and agree
    if pred == 1:
        okc = True
        xs = [construct(n, list(ds), w) for w in (0, 1)]
        okc = xs[0] != xs[1]
        for x in xs:
            okc = okc and P.relative_interior_contains(vector(QQ, [x[k] for k in U]))
        msg.append('two constructed points interior: %s' % okc)
        ok = ok and okc
    if not ok: bad += 1
    print('n=%d d=%s D=%d #pts=%d #int(P)=%d #int(2P)=%s codeg=%s predicted=%d %s %s'
          % (n, ds, D, len(pts), i1, i2, codeg, pred, 'OK' if ok else 'FAIL', '; '.join(msg)), flush=True)
print('cases', len(cases), 'failures', bad, flush=True)
