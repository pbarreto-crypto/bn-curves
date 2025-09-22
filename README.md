This crate implements elliptic curve arithmetic and bilinear pairings for Barreto-Naehrig (BN) curves.
It was created to commemorate the 20th anniversary of the discovery of those curves in 2005.

A BN curve is specified by an integer parameter <i>u</i> &#8712; &Zopf; such that the value
<i>p</i> &#x2254; 36<i>u&#x2074;</i> + 36<i>u&sup3;</i> + 24<i>u&sup2;</i> + 6<i>u</i> + 1 is prime,
defining a finite field <b>F</b><sub><i>p</i></sub>.

The additional constraint <i>p</i> &equiv; 3 (mod 4) is typical, since it enables specifying
the quadratic extension <b>F</b><sub><i>p&sup2;</i></sub> = <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2;</i> + 1&gt;
and the tower-friendly extension fields
<b>F</b><sub><i>p&#x2074;</i></sub> &simeq; <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&sigma;</i>&rbrack;/&lt;<i>&sigma;&sup2; - &xi;</i>&gt;,
<b>F</b><sub><i>p&#x2076;</i></sub> &simeq; <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&tau;</i>&rbrack;/&lt;<i>&tau;&sup3; - &xi;</i>&gt;,
and <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> &simeq; <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076; - &xi;</i>&gt;,
where <i>&xi;</i> = 1 + <i>i</i>.

The BN curve equation is <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>,
whose number of points is
<i>n</i> &#x2254; <i>#E</i>(<b>F</b><sub><i>p</i></sub>) = <i>36u&#x2074;</i> + 36<i>u&sup3;</i> + 18<i>u&sup2;</i> + 6<i>u</i> + 1,
which is usually required (with a careful choice of the curve parameter <i>u</i>) to be prime.
The underlying finite field and the number of points are thus related as
<i>n</i> = <i>p</i> + 1 - <i>t</i> where <i>t</i> &#x2254; 6<i>u&sup2;</i> + 1 is the trace of the Frobenius endomorphism
on the curve.
Incidentally, the curve order satisfies <i>n</i> &equiv; 5 (mod 8).

The default quadratic twist of the curve is <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3; + b'Z'&sup3;</i>
with <i>b'</i> &#x2254; <i>b</i>/<i>&xi;</i>, whose number of points is <i>n'</i> &#x2254;
<i>#E'</i>(<b>F</b><sub><i>p&sup2;</i></sub>) = <i>h'</i><i>n</i>
where <i>h'</i> &#x2254; <i>p</i> - 1 + <i>t</i> is called the cofactor of the curve twist.

All supported curves were selected so that the BN curve parameter is a negative number
(so that field inversion can be replaced by conjugation at the final exponentiation of a pairing)
with absolute value of small Hamming weight (typically 5 or less),
ceil(lg(<i>p</i>)) = 64&times;<i>LIMBS</i> - 2 for 64-bit limbs,
and the curve equation coefficients are always <i>b</i> = 2 and <i>b'</i> = 1 - <i>i</i>.

With this choice, a suitable generator of <i>n</i>-torsion on <i>E</i>/<b>F</b><sub><i>p</i></sub>
is the point <i>G</i> &#x2254; &lbrack;-1 : 1 : 1&rbrack;,
and a suitable generator of <i>n</i>-torsion on <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub>
is the point <i>G'</i> &#x2254; &lbrack;<i>h'</i>&rbrack;<i>G&#x2080;'</i>
where <i>G&#x2080;'</i> &#x2254; &lbrack;-<i>i</i> : 1 : 1&rbrack;.
The maximum supported size is <i>LIMBS</i> = 12.

All feasible care has been taken to make sure the arithmetic algorithms adopted in this crate
are isochronous ("constant-time") and efficient.
Yet, the no-warranty clause of the MIT license is in full force for this whole crate.

References:

* Paulo S. L. M. Barreto, Michael Naehrig:
"Pairing-Friendly Elliptic Curves of Prime Order."
In: Preneel, B., Tavares, S. (eds). <i>Selected Areas in Cryptography -- SAC 2005</i>.
Lecture Notes in Computer Science, vol. 3897, pp. 319--331.
Springer, Berlin, Heidelberg. 2005. https://doi.org/10.1007/11693383_22

* Geovandro C. C. F. Pereira, Marcos A. Simplicio Jr., Michael Naehrig, Paulo S. L. M. Barreto:
"A Family of Implementation-Friendly BN Elliptic Curves."
<i>Journal of Systems and Software</i>, vol. 84, no. 8, pp. 1319--1326.
Elsevier, 2011. https://doi.org/10.1016/j.jss.2011.03.083
