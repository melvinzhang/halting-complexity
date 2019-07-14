# extracted from "The Riemann Hypothesis in Computer Science" by Yuri Matiyasevich
# n!! is the product of all the integers from 1 up to n that have the same parity (odd or even) as n

# d(1) = 0
# d(n+1) = 2nd(n) - (-1)^n (2n - 2)!!

# q(1) = 1
# q(n+1) = (n+1)q(n)/g(n+1)
# where g(m) = GCD(m, q(m-1))

# p(1) = 0
# p(n+1) = p(n) + 1 if g(n) = 1
#          p(n) otherwise

# f0(1) = 1
# f0(n+1) = (2n+2)f0(n)

# f3(1) = 1
# f3(n+1) = (2n+5)f3(n)

# l(n) = floor(log_2(q(n)))
# p(n)^2(d(n)l(n) - f0(n)) < f3(n) all n = 1... iff the Riemann Hypothesis is true

from math import gcd
d=m=p=0
f0=f1=f3=n=q=1
while p**2*(m-f0)<f3:
  print(n,p)
  d=2*n*d-(-1)**n*f1
  n=n+1
  g=gcd(n,q)
  q=n*q//g
  if g==1: p=p+1
  m=d*(q.bit_length()-1)
  f1=2*f0
  f0=2*n*f0
  f3=(2*n+3)*f3
