"""Exact point, hull, support and disk witnesses in Q(sqrt(3)).

Arithmetic from the project’s independent ordered-tree consumer.
"""
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
import math

def sg(z):
    a,b=z
    if a==0:return (b>0)-(b<0)
    if b==0 or (a>0)==(b>0):return (a>0)-(a<0)
    q=a*a-3*b*b
    return ((q>0)-(q<0))*((a>0)-(a<0))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[0],-a[1]
def sub(a,b):return add(a,neg(b))
def mul(a,b):return a[0]*b[0]+3*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def scale(k,a):return k*a[0],k*a[1]
def sq(a):return mul(a,a)
def rt(a):return 3*a[1],a[0]
def vd(a,b):return sub(a[0],b[0]),sub(a[1],b[1])
def dot(a,b):return add(mul(a[0],b[0]),mul(a[1],b[1]))
def cross(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
def decode(values):
    if not isinstance(values,(list,tuple)) or not values or any(
        not isinstance(p,(list,tuple)) or len(p)!=3 or any(type(c) is not str for c in p)
        for p in values):
        raise ValueError('nonempty exact string-triple point list required')
    q=[tuple(Fraction(c) for c in p) for p in values]
    D=math.lcm(*(c.denominator for p in q for c in p))
    points=[((int(x*D),0),(int(y*D),int(b*D))) for x,y,b in q]
    return points,D
def compare(a,b):
    x=sg(sub(a[0],b[0]));return x or sg(sub(a[1],b[1]))
def hull(P):
    P=sorted(set(P),key=cmp_to_key(compare))
    if len(P)<=1:return P
    def chain(seq):
        out=[]
        for p in seq:
            while len(out)>1 and sg(cross(vd(out[-1],out[-2]),vd(p,out[-1])))<=0:out.pop()
            out.append(p)
        return out
    return chain(P)[:-1]+chain(reversed(P))[:-1]
def diameter_witness(P,D):
    for i,j in combinations(range(len(P)),2):
        e=vd(P[i],P[j]);ex=sub(dot(e,e),(D*D,0))
        if sg(ex)>0:return {'pair':[i,j],'excess_integer_ring':ex,'denominator_squared':D*D}
    return None
def support_events(P,D):
    H=hull(P)
    if len(H)<2:return None
    out=[]
    for i,a in enumerate(H):
        b=H[(i+1)%len(H)];e=vd(b,a);n=(e[1],neg(e[0]))
        n0=(scale(2,n[0]),scale(2,n[1]))
        n1=(sub(neg(n[0]),rt(n[1])),sub(rt(n[0]),n[1]))
        n2=(neg(add(n0[0],n1[0])),neg(add(n0[1],n1[1])))
        total=(0,0);supports=[]
        for direction in (n0,n1,n2):
            vals=[dot(direction,p) for p in H]
            k=max(range(len(H)),key=cmp_to_key(lambda j,k:sg(sub(vals[j],vals[k]))))
            total=add(total,vals[k]);supports.append(k)
        if sg(total)<0:raise ValueError('support sum must be nonnegative')
        gap=sub(sq(total),scale(3*D*D,dot(e,e)))
        if sg(gap)<=0:return None
        out.append({'edge':i,'supports':supports,'strict_squared_gap':gap})
    return {'hull':H,'denominator':D,'all_events':out}
def disk_witness(P,D,R):
    # Every convex set containing P contains every closed segment between P.
    rn,rd=R.numerator,R.denominator
    def radial(p):return sub(scale(rd,dot(p,p)),(rn*D*D,0))
    for i,p in enumerate(P):
        v=radial(p)
        if sg(v)<0:return {'point':i,'strict_scaled_radial_gap':v}
    for i,j in combinations(range(len(P)),2):
        a,b=P[i],P[j];e=vd(b,a);den=dot(e,e);projection=neg(dot(a,e))
        if sg(projection)<=0 or sg(sub(den,projection))<=0:continue
        v=sub(mul(radial(a),den),scale(rd,sq(projection)))
        if sg(v)<0:return {'segment':[i,j],'strict_scaled_radial_gap':v,'projection':projection,'segment_norm_squared':den}
    return None
def prove(values,code,R):
    if type(code) is not int or code not in (1,2,3):raise ValueError('unsupported claimed code')
    if code==3 and (type(R) is not Fraction or R<=0):raise ValueError('positive exact squared radius required')
    P,D=decode(values)
    if code==1:return diameter_witness(P,D)
    if code==2:return support_events(P,D)
    if code==3:return disk_witness(P,D,R)
    raise ValueError('unsupported claimed code')
