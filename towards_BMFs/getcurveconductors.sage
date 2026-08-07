from sage.all import QQ, PolynomialRing;
from picard_curves import PicardCurve;
R = PolynomialRing(QQ,'x');
load('../nonsurj7.sage');

len(curves)
fil = open('../curve_conductors.txt', 'a')
for n in range(33,len(curves)):
    try:
        C = curves[n]
        NC = PicardCurve(R(C)).cond
        fil.write(str(C)+":"+str(NC)+"\n")
    except:
        pass

fil.close()

/*
[1, 2, 4, 2, 1]
[(2, 12), (3, 9), (5, 2)]
[2, 4, 8, 4, 2]
[(2, 12), (3, 6), (5, 2)]
[1, 4, 8, 8, 8]
[(2, 12), (3, 9), (5, 2)]
[-3, 26, -74, 68, 4]
[(2, 8), (3, 9), (7, 6)]
[3, 6, 12, 6, 3]
[(2, 12), (3, 15), (5, 2)]
[0, 2, 42, 289, 648]
We make the coordinate change (x --> 1/81*x) in order to work                with an integral polynomial f
[(2, 6), (3, 5), (7, 2)]
[0, 5, 45, 132, 125]
[(3, 15), (5, 4)]
[-3, 8, 30, 0, 1]
[(2, 14), (3, 15)]
[5, 10, 20, 10, 5]
[(2, 12), (3, 9), (5, 6)]
[-6, 52, -148, 136, 8]
[(2, 10), (3, 9), (7, 6)]
[-7, 36, -48, 8, 12]
We make the coordinate change (x --> 1/3*x) in order to work                with an integral polynomial f
[(2, 14), (3, 13)]
[6, 12, 24, 12, 6]
[(2, 12), (3, 15), (5, 2)]
[0, 4, 84, 578, 1296]
We make the coordinate change (x --> 1/81*x) in order to work                with an integral polynomial f
[(2, 8), (3, 9), (7, 2)]
[5, 28, 36, 8, 4]
[(2, 12), (3, 15)]
[7, 14, 28, 14, 7]
[(2, 12), (3, 6), (5, 2), (7, 6)]
[0, 10, 90, 264, 250]
[(2, 6), (3, 15), (5, 4)]
[4, 24, 36, 12, 9]
We make the coordinate change (x --> 1/3*x) in order to work                with an integral polynomial f
[(2, 14), (3, 15)]
[3, 12, 24, 24, 24]
[(2, 12), (3, 15), (5, 2)]
[-9, 78, -222, 204, 12]
[(2, 8), (3, 15), (7, 6)]
[44, -56, 0, 20, 1]
[(2, 14), (3, 13)]
[9, 18, 36, 18, 9]
[(2, 12), (3, 15), (5, 2)]
[0, 5, 90, 528, 1000]




AssertionError: We failed to compute the semistable reduction of Picard curve y^3 = 8*x^4 + 16*x^3 + 72*x^2 + 56*x + 10 over Rational Field at 2

see the result in curve_conductors.txt
It has result for 33 curves.
The process on lovelace was killed, presumably because it was taking too much memory.
*/


