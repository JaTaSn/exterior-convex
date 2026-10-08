# Linusson eq (14) reproduced, and our p-polynomials in his binomial base

Run 2026-10-04, jts-yoga. Script: `code/oneoff/linusson_eq14_binomial_base.py`, which carries
the full reading of the result in its header.

```
Linusson's equation (14), recomputed from his recursion, in base C(p+2,j):
  F^p(0) = 2
  F^p(1) = C(p+2,1)
  F^p(2) = C(p+2,3) - C(p+2,2) + 2 C(p+2,1) - 1
  F^p(3) = 4 C(p+2,6) + C(p+2,4) + C(p+2,1)
  F^p(4) = 120 C(p+2,10) + 188 C(p+2,9) + 95 C(p+2,8) + 18 C(p+2,7) + 5 C(p+2,6) + C(p+2,4) + C(p+2,1)

 n d          deg  coefficients in base C(p+2,j), high->low
 2 (0, 0)       3  [6, -7, 11, -12]   has negatives
 2 (0, 1)       5  [10, 2, 4, -2, 4, -2]   has negatives
 2 (0, 0, 0)    3  [18, -22, 32, -38]   has negatives
 2 (0, 1, 2)    7  [210, 230, 120, 16, 18, -10, 15, -12]   has negatives
 3 (0, 0)       6  [56, -8, 19, -14, 14, -11, 11]   has negatives
 3 (0, 1)       9  [336, 672, 427, 118, 16, 7, -1, 3, -1, 3]   has negatives
 3 (0, 4)      12  [14784, 44352, 52080, 30912, 10150, 1988, 274, 30, 9, 0, 2, 1, 0]   ALL >= 0
 3 (0, 1, 3)   14  [2690688, 11147136, 19034400, 17367504, 9194808, 2884476, 532098, 57652, 4093, 316, 25, 20, -10, 16, -14]   has negatives
 3 (0, 2, 3)   14  [2690688, 10570560, 17201184, 15048264, 7708680, 2377200, 444010, 51121, 4011, 294, 47, -2, 12, -6, 8]   has negatives
```
