import math, json
import numpy as np
from scipy.optimize import brentq

def chord(m,a,b):
    R=math.sqrt(1+(1-a*a)*(1-b))
    # Positive finite sum is stable near coincident endpoints.
    return sum(a**k*R**(m-k) for k in range(m+1))/(m+1)
if __name__=='__main__':
    for m in [7,10,15,20,30,44]:
        a=.9;h=1-a
        b=brentq(lambda b:chord(m,a,b)-1,0,.99)
        cand=((m-4)*h+3*h*h)/(3+m*h)
        print(m,b,cand,chord(m,a,cand))
