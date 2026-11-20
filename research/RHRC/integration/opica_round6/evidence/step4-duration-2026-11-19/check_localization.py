"""Directed checks of the constants in the complete-source smooth partition."""
import json
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx

ctx.prec = 180
q = arb(101)/100
height = 3*10**12
scale = 10**6
tail_start = height - 1010001
g = 2*(10000+arb(374)/1000)/tail_start**2
ell = arb(227)/10**21
margin = ell*q.log()-g
strip_margin = ell*q.log()-2*(10000+arb(1)/2)/tail_start**2
rate = scale*(1-(1+q.log())/q)
assert margin > arb(3)/10**23
assert strip_margin > arb(3)/10**23
assert rate > 40
assert Fraction(101,100)**2*Fraction(227,10**21)/scale < Fraction(233,10**27)
assert Fraction(101,100)*(Fraction(201,100))/scale < 2-Fraction(1,4096)
b = Fraction(37335,100000)
assert b/(height**2-b*b)<Fraction(415,10**28)<Fraction(5,10**26)
assert 8*Fraction(1,8)<=1
data={"qualification":"Finite scalar margins for the paper proof. No cofinal arithmetic upper.",
      "maximum_right_mode_log_gain_per_order":str(g),"discarded_right_mode_log_decay_per_order_at_least":str(margin),
      "discarded_right_mode_log_decay_using_only_critical_strip":str(strip_margin),
      "large_time_decay_in_retained_weight_per_unit_time":str(rate),
      "lambda":scale,"order_coefficient":"2.27e-19","upper_log_prime_slope":"2.33e-25",
      "gaussian_threshold_upper":"4.15e-26","fixed_cutoff":10000000}
Path(__file__).with_name("LOCALIZATION_CONSTANTS.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
print("PASS",margin,rate)
