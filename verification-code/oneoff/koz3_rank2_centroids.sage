# koz3_rank2_centroids.sage -- 2026-11-07, Claude-Code (jts-mini), at Jan's request.
# Exact vertices, facets, lattice points and the five centroids of prop-pushforward (Part III) for
# Koz(3;0,1) and Koz(3;0,2). Explained in ../../working-notes/koz3-rank-two-pictures.org.
# Output on 2026-11-07 (SageMath 10.9), in (x2,x3,x4) resp. (x2,x3,x4,x5):
#   d=(0,1): dim 3, 7 vertices, 6 facets, volume 6; 22 ff-vectors = 22 lattice points; collisions at
#     (6,1,0),(6,2,0),(6,3,0); c(FF) = c(lattice) = (51/11,2,5/22); indep c(S3) = (24/5,2,1/5);
#     c(Koz) = (37/8,7/3,3/8); indep c(Koz3) = (5,7/3,1/3)
#   d=(0,2): dim 4, 9 vertices, 6 facets, volume 9/4; 25 ff-vectors = 25 lattice points, no collisions;
#     c(FF) = c(lattice) = indep c(S3) = (14/5,16/5,9/5,1/5); c(Koz) = indep c(Koz3) = (3,10/3,2,1/3)
# Run: sage code/oneoff/koz3_rank2_centroids.sage

print('== d = (0,1)')
S3 = [(0,0),(1,0),(2,0),(3,0),(3,1)]          # (f2,f3) of proper complexes on [3]; f0=1, f1=3
V3 = [(0,0),(3,0),(3,1)]                      # vertices of Koz(3) in (x2,x3)
K = Polyhedron(vertices=V3)
print("Koz(3): centroid", K.centroid(), " c(S3)", tuple(sum(QQ(p[i]) for p in S3)/len(S3) for i in range(2)), " lattice pts", sorted(tuple(p) for p in K.integral_points()))
# sum in (x2,x3,x4): (a,b) from summand 1 gives (a,b,0); (a',b') from the shifted summand gives (3,a',b')
emb1 = lambda p: vector(QQ,(p[0],p[1],0)); emb2 = lambda p: vector(QQ,(3,p[0],p[1]))
P = Polyhedron(vertices=[emb1(u)+emb2(v) for u in V3 for v in V3])
print("sum: dim", P.dim(), "vertices", P.n_vertices(), "facets", P.n_facets(), "volume", P.volume())
verts = set(tuple(v) for v in P.vertex_generator())
for u in V3:
    for v in V3:
        w = tuple(emb1(u)+emb2(v)); print("  ", u, "+ shift", v, "->", w, "VERTEX" if w in verts else "")
FF = {}
for u in S3:
    for v in S3:
        w = tuple(emb1(u)+emb2(v)); FF[w] = FF.get(w,0)+1
L = [tuple(p) for p in P.integral_points()]
cen = lambda pts: tuple(sum(QQ(p[i]) for p in pts)/len(pts) for i in range(3))
print("FF distinct", len(FF), "(pairs 25), lattice", len(L), "FF==lattice", set(FF)==set(L))
print("collisions:", {w:m for w,m in FF.items() if m>1})
print("c(FF)       ", cen(list(FF)))
print("c(lattice)  ", cen(L))
print("indep c(S3) ", tuple(emb1((QQ(9)/5,QQ(1)/5))+emb2((QQ(9)/5,QQ(1)/5))))
print("c(Koz(3;0,1))", tuple(P.centroid()))
print("indep c(Koz3)", tuple(emb1((2,QQ(1)/3))+emb2((2,QQ(1)/3))))
print("pushforward of uniform on S3^2 (with multiplicity):", tuple(sum(m*QQ(w[i]) for w,m in FF.items())/25 for i in range(3)))

print('== d = (0,2)')
S3 = [(0,0),(1,0),(2,0),(3,0),(3,1)]; V3 = [(0,0),(3,0),(3,1)]
# d=(0,2): (1,3,a,b,0,0) + (0,0,1,3,a',b') = (1,3,a+1,b+3,a',b'); coordinates (x2,x3,x4,x5)
emb1 = lambda p: vector(QQ,(p[0],p[1],0,0)); emb2 = lambda p: vector(QQ,(1,3,p[0],p[1]))
P = Polyhedron(vertices=[emb1(u)+emb2(v) for u in V3 for v in V3])
print("sum: dim", P.dim(), "vertices", P.n_vertices(), "facets", P.n_facets(), "volume", P.volume())
verts = set(tuple(v) for v in P.vertex_generator())
print("all 9 pairs vertices:", all(tuple(emb1(u)+emb2(v)) in verts for u in V3 for v in V3))
for f in P.inequality_generator(): print("  ", f)
FF = {}
for u in S3:
    for v in S3:
        w = tuple(emb1(u)+emb2(v)); FF[w] = FF.get(w,0)+1
L = [tuple(p) for p in P.integral_points()]
cen = lambda pts: tuple(sum(QQ(p[i]) for p in pts)/len(pts) for i in range(4))
print("FF distinct", len(FF), "collisions", sum(1 for m in FF.values() if m>1), "lattice", len(L), "FF==lattice", set(FF)==set(L))
print("c(FF)        ", cen(list(FF)))
print("c(lattice)   ", cen(L))
print("indep c(S3)  ", tuple(emb1((QQ(9)/5,QQ(1)/5))+emb2((QQ(9)/5,QQ(1)/5))))
print("c(Koz(3;0,2))", tuple(P.centroid()))
print("indep c(Koz3)", tuple(emb1((2,QQ(1)/3))+emb2((2,QQ(1)/3))))
