Halting complexity of mathematical statements
=============================================

The halting complexity of a mathematical statement is the size of the smallest
program that halts if the statement is false and runs forever if the statement
is true.

Erdős ternary digit conjecture
------------------------------

There is least one digit 2 in the base 3 representation of $2^n$ for $n \gt 8$.

[Stérin and Woods 2021](https://arxiv.org/abs/2107.12475) describes two small Turing machine that half if and only if the conjecture is false.
* [5-state 4-symbol Turing machine](https://github.com/tcosmo/bbsim/blob/main/machines/powers_of_two_5_4.txt)
* [15-state 2-symbol Turing machine](https://github.com/tcosmo/bbsim/blob/main/machines/powers_of_two_15_2.txt)

Riemann Hypothesis
------------------

Programs published in [The Riemann Hypothesis in Computer Science](https://researchspace.auckland.ac.nz/bitstream/handle/2292/45072/527.pdf) by Yuri Matiyasevich.
* [14 line Python3 program](riemann-hypothesis/rh.py)
* [128 line Register Machine program](riemann-hypothesis/rh.rm)

Legendre's Conjecture
---------------------
For any natural number n, there exists a prime number p such that n^2 <= p <= (n+1)^2.

Checked by enumerating all n and testing if there is a prime p within [n^2, (n+1)^2]

Fermat's Last Theorem
---------------------
There are no positive integers x,y,z satisfying x^n + y^n = z^n for any integer n > 2

Checked by enumerating all tuples of (x,y,z,n) and checking for a case where x^n + y^n = z^n

Dyson's conjecture
----------------
The reverse of a power of two is never a power of 5

Enumerate all powers of two and check if it is a power of 5

ZFC + SRP is consistent
-----------------------
[Yedidia and Aaronson](https://arxiv.org/abs/1605.04343) gave a 7,910-state Turing machine with 1 tape and a 2-symbol alphabet

ZFC is consistent
-----------------
[Stefan O’Rear](https://github.com/sorear/metamath-turing-machines) gave a 1919 state Turing machine with 1 tape and 2-symbol alphabet

References
----------
* [Algorithmic Complexity of Mathematical Problems: An Overview of Results and Open Problems](https://www.cs.auckland.ac.nz/~cristian/crispapers/ComplexityMathProblemOpen.pdf)

Talks
-----
* [The complexity of mathematical problems: an overview of results and open problems](https://vimeo.com/34124468)
