# extracted from "The Riemann Hypothesis in Computer Science" by Yuri Matiyasevich
from math import gcd
d=m=p=0
f0=f1=f3=n=q=1
while p**2*(m-f0)<f3:
  d=2*n*d-(-1)**n*f1
  n=n+1
  print(n)
  g=gcd(n,q)
  q=n*q//g
  if g==1: p=p+1
  m=0; q2=q
  while q2>1:
    q2=q2//2; m=m+d
  f1=2*f0
  f0=2*n*f0
  f3=(2*n+3)*f3
