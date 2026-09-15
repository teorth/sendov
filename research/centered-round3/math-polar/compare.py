"""High-precision ORIGINAL-C versus structural tails on an exact feasible family.
The feasibility and the extended-chord obstruction are proved separately by verify.py.
This file's decimal outputs are numerical comparisons, not interval certificates.
"""
import json
from pathlib import Path
import mpmath as mp

def run(dps):
    mp.mp.dps=dps
    m=44;a=mp.mpf(9)/10;x=u=mp.mpf(177)/250;s=mp.mpf(1);v=s-u*u
    z=a*u;w=1-z;gamma=v/((m-1)*u*u);D=m*(m-1)*(m-2)
    S=mp.mpf(9)/4-mp.mpf(2)/(m-1)-mp.mpf(1)/(2*m*(m-1));eta=2*mp.sqrt(S)/3
    B2=sum(mp.binomial(m+1,j)*z**j*(1-z)**(m+1-j) for j in range(3))
    terms=[];maxerr=mp.mpf(0)
    for k in range(3,m+1):
        C=mp.sqrt(v**k*(mp.mpf(m)**m/(mp.mpf(k)**k*mp.mpf(m-k)**(m-k)) if k<m else 1))
        H=sum(mp.binomial(m+1,j)*z**j*(1-z)**(m+1-j) for j in range(k+1,m+2))
        H2=(m+1)*mp.binomial(m,k)*z**(k+1)*mp.quad(lambda t:t**k*(1-z*t)**(m-k),[0,1])
        maxerr=max(maxerr,abs(H-H2))
        terms.append(C*H/(mp.binomial(m,k)*u**k))
    literal=sum(terms)
    beta=lambda t:1-2*a*x*t+a*a*s*t*t
    betaI=mp.quad(lambda t:t**3*beta(t)**((m-3)/2),[0,mp.mpf('.5'),1])
    pref=mp.sqrt(S)*(m+1)*a**4*u*v**mp.mpf('1.5')*mp.sqrt(D)
    structural=pref*betaI
    d=1-mp.sqrt(beta(1))
    finite_chord=pref*mp.quad(lambda t:t**3*(1-d*t)**(m-3),[0,1])
    extended=9*eta*a**4*u*v**mp.mpf('1.5')/(d**4*mp.sqrt(D))
    full=mp.quad(lambda t:(a*a+2*a*(1-a*a)*x*t+(1-a*a)**2*s*t*t)**(m/2),[0,1])
    budget=1-a*u
    common=w**(m+1)+gamma*(1+B2)
    assert maxerr<mp.mpf(10)**(-dps+15)
    assert literal<structural<finite_chord<extended
    data={'dps':dps,'full_complex_integral':full,'target_budget':budget,'literal_C_tail':literal,'structural_beta_tail':structural,'finite_norm_chord_tail':finite_chord,'extended_norm_chord_tail':extended,'literal_C_total_ratio':(common+literal)/budget,'structural_total_ratio':(common+structural)/budget,'finite_chord_total_ratio':(common+finite_chord)/budget,'extended_chord_total_ratio':(common+extended)/budget,'H_identity_max_error':maxerr}
    return {k:(mp.nstr(val,60) if k!='dps' else val) for k,val in data.items()}
if __name__=='__main__':
    rows=[run(90),run(160)]
    for key in rows[0]:
        if key not in ('dps','H_identity_max_error'):
            assert abs(mp.mpf(rows[0][key])-mp.mpf(rows[1][key]))<mp.mpf('1e-55')
    out=Path(__file__).with_name('cache');out.mkdir(exist_ok=True)
    (out/'tail-comparison.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows,indent=2))
