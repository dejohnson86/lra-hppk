import time
from sage.plot.histogram import Histogram
from sage.modules.misc import gram_schmidt

'''
32 bit prime: 3320833723
72: 4681074808958153331041
136: 60475045147803217722699504640873937294951
174: 23639474998292043714787719276401511591355325698674617
256: 94067902964486534841221493569020601188977813763773733271352395468028284646947

128: 340282366920938463463374607431768211297
192: 5942469270856831795917092266069695163680807107647946407181
256: 58404419428506214291982011245145040181275199295816272238310291089757935381339
'''

#####################################
### Universal Variables

p=17065242806912356291

md=2*ceil(log(p,2))+8
L=round(log(p,2))
TLL=2**md
TUL=2*TLL

TPL=2**(3*ceil(log(p,2))+8)
TPU=2*TPL

Z.<z>=PolynomialRing(GF(p))
X.<x>=PolynomialRing(ZZ)

#####################################
### Auxiliary Functions

def l2(n):
	m=log(abs(n),2)
	return(RR(m))

def rply(degr):
	ply=0
	for i in range(degr+1):
		ply=ply+randint(2,p-1)*z**i
	return(ply)
	
def EL(ly,Rx,tx):
	ly2=[]
	for i in range(len(ly)):
		ly2+=[Rx*ly[i]%tx]
	return(ly2)

def mtr(n,R1,T1):
	return((R1*n-(R1*n)%T1)/T1)

def coefflims(vec):
	for i in range(6):
		if (vec[i]<1) or (vec[i]>p-1):
			return(False)
	return(True)


def gcdoutV(vec):
	ind=0
	while vec[ind]==0:
		ind+=1
	cv=gcd(vec[ind],vec[ind+1])
	if cv==1:
		return(vec,1)
	for i in range(ind+1,5):
		cv=gcd(cv,vec[i])
	vnew=vector(ZZ,copy(vec)/cv)
	return(vnew,cv)

#####################################
### Encryption and Decryption
	
def eval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]	
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)
						

def preval(Py,Ly):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Ly[0]^i)*Ly[j]%p]
	return(aL)

def encryptHPPK(pp1,pp2,mu1u2):
	C=[]
	C+=[eval(pp1,mu1u2)]
	C+=[eval(pp2,mu1u2)]
	return(C)	
	
def decryptHPPK(sp1,sp2,Ri1,Ri2,t1,t2,C):
	r1=Ri1*C[0]%t1
	r2=Ri2*C[1]%t2
	fp=sp1-GF(p)(r1/r2)*sp2
	m=fp.roots()[0]
	return(m)
	
#####################################
### Key Generation

def skpkgen(ix):
	if ix:
		t=randint(TLL,TUL)
		q=randint(TLL,TUL)
	else:
		t=randint(TPL,TPU)
		q=randint(TPL,TPU)
		
	f=rply(1)
	h=rply(1)

	B=[rply(1),rply(1)]

	P=[X(f*b) for b in B]
	Q=[X(h*b) for b in B]

	Ps=P[0].coefficients(sparse=False)+P[1].coefficients(sparse=False)
	Qs=Q[0].coefficients(sparse=False)+Q[1].coefficients(sparse=False)
	
	Pmin=min(Ps)
	Qmin=min(Qs)
	RLL=ceil(t/Pmin)
	SLL=ceil(q/Qmin)
	
	R=0
	while (gcd(R,t)!=1):	
		R=randint(RLL,t)
	S=0
	while (gcd(S,q)!=1):	
		S=randint(SLL,q)
		
	Ri=xgcd(R,t)[1]%t
	Si=xgcd(S,q)[1]%q

	vPs=vector(Ps)
	VP2s=copy(vPs)
	vQs=vector(Qs)
	VQ2s=copy(vQs)
	for i in range(6):
		VP2s[i]+=p*randint(1,p)
		VQ2s[i]+=p*randint(1,p)
	ZP=Z(list(vPs))
	ZQ=Z(list(vQs))
	if ix:
		Pp=EL(Ps,R,t)
		Qp=EL(Qs,S,q)
	else:
		Pp=EL(VP2s,R,t)
		Qp=EL(VQ2s,S,q)
	Pp=vector(ZZ,Pp)
	Qp=vector(ZZ,Qp)

	bPv=vector([mtr(i,R,t) for i in Ps])	
	bQv=vector([mtr(i,S,q) for i in Qs])

	MP=matrix(ZZ,[vPs,bPv])
	MQ=matrix(ZZ,[vQs,bQv])
	
	sk=[[Ps,[t,R,Ri]],[Qs,[q,S,Si]]]
	pk=[Pp,Qp]
	if ix:
		return(sk,pk,[MP,MQ])
	else:
		return(sk,pk,[MP,MQ],[VP2s,VQ2s])
#########################################
### Evolved Lattice Reconstitution Attack
#########################################
### Major Form ###

def ELRA(PK):
	SA=[]
	TFA=[]
	for i in range(2):
		SA+=[ELRAhalfstart(PK[i])]
	TSigma=divizer(SA[0])
	for i in range(2):
		TFA+=[finalizer(PK[i],TSigma[i],SA[i][1])]
	return(TFA)	

def ELRAhalfstart(pkH):
	PFA=[]
	D=discriminator(pkH)
	SR=SRoots(pkH)
	return(SR)

def divizer(LT):
	L1=[]
	L2=[]
	for el in LT[0][0]:
		L1+=[Z(list(el))]
	for el in LT[1][0]:
		L2+=[Z(list(el))]		
	for el1 in L1:
		for el2 in L2:
			dp=gcd(el1,el2).degree()
			if dp>=4:
				return(el1,el2)
	
	
def finalizer(pkH,tsigma,EFM): 
	PFA+=[SRecover(EFM,vector(ZZ,tsigma))]
	FA=[]
	for ax in PFA:
		at=gcdoutV(ax[1])[0]
		tp=gcdoutV(D*at)[1]
		ind=0
		while(gcd(tp,at[ind])!=1):
			ind+=1
			
		Rp=xgcd(at[ind],tp)[1]*pkH[ind]%tp
		FK=Rp*at%tp
		if vector(ZZ,pkH)==vector(ZZ,FK):
			return(at,Rp,tp)		


### Echelon Discriminator Component ###

def EDC(PK):
	Mat=discriminator(PK)
	D=Mat.LLL()
	D=D.matrix_from_rows(range(4))
	D=D.right_kernel().matrix()
	return(D)

def discriminator(pkL):
	rl=[]
	r2=[]
	LY=xgcdList(pkL)
	ln=len(LY)
	for i in range(ln):
		for j in range(i+1,ln):
			if LY[i][2][0]==LY[j][2][0]:
				rl+=[eqsm(LY[i],LY[j])]
				
			else:
				X1=LY[j][2][0]*vector(ZZ,LY[i][2])
				X2=LY[i][2][0]*vector(ZZ,LY[j][2])
				L1M=LY[i][:2]+[X1]
				L2M=LY[j][:2]+[X2]
				rl+=[eqsm(L1M,L2M)]
	r1=matrix(rl)
	r1=r1.echelon_form()
	r1=r1[:r1.rank()]
	
	for i in range(5):
		cv=gcd(r1[i][i],r1[i][5])
		if cv>1:
			for j in range(5):	
				if r1[i][j]!=0:
					cv=gcd(cv,r1[i][j])	
		r2+=[r1[i]/cv]
	r2=matrix(ZZ,r2)
	return(r2)

def xgcdList(LP):
	coll=[]
	for i in range(5):
		for j in range(i+1,6):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)

def eqsm(L1,L2):
	fineq=[0 for i in range(6)]
	g0123=[L1[2][1],L1[2][2],L2[2][1],L2[2][2]]
	for i in range(4):
		if i<2:
			fineq[L1[i]]+=g0123[i]
		else:
			fineq[L2[i%2]]-=g0123[i]
	return(fineq)
			
### Final Secret Recovery Component ###

def SRecover(EM,vf):
	Tv=[]
	for i in range(6):
		ZF=[]
		for j in range(5):
			cf=randint(1,p)
			ZF+=[cf*vf%p]
			
		A=EM.stack(matrix(ZF))
		KAv=vector((A.left_kernel()).matrix()[0])
		Tv+=[KAv[2:]*A[2:]]
	TV=(matrix(Tv).LLL())[4:]
	TT=copy(TV)
	TT[0]*=TT[0][0].sign()
	TT[1]*=TT[1][0].sign()
	return(TT)	
		
def SRoots(pkH):
	M=EDC(pkH)
	N=matrix(GF(p),copy(M))
	if N[1][1]==0:
		print(N[0])
		print(N[1])
	if N[0][0]==0:
		print(N[0])
		print(N[1])
	N[1]=N[1]/N[1][1]
	N[0]=N[0]/N[0][0]
	U=VecToMat(N)
	Sply=plyfourth(U[0],U[1])
	rts=Sply.roots()
	Fposs=[]
	for r in rts:
		vr=vector(GF(p),[1,r[0],r[0]^2])
		mp=-vr*U[0][0]/(vr*U[1][0])
		vp=vector(GF(p),list(U[0][0]+mp*U[1][0])+list(U[0][1]+mp*U[1][1]))
		Fposs+=[vp]
	return(Fposs,M)
	
def VecToMat(M):
	Tm=matrix(GF(p),[M[0][:3],M[0][3:]])
	Am=matrix(GF(p),[M[1][:3],M[1][3:]])
	return(Tm,Am)

def plyfourth(T,A):
	Gam=z+A[0][2]*z^2
	Bet=-1-T[0][1]*z-T[0][2]*z^2
	Phi=(T[1][0]+T[1][1]*z+T[1][2]*z^2)*Gam+Bet*(A[1][0]+A[1][1]*z+A[1][2]*z^2)
	return(Phi)


#########################################
### ELRA Mass Tester
#########################################

def ELRAMass(ntests):
	timestart=time.time()
	rtcases=0
	maxval=0
	normllp=0
	maxdenom=0
	maxnum=0
	for i in range(ntests):
		K=skpkgen(True)
		ANS=ELRAM1(K)
		
		for J in ANS:
			for jv in J:
				fmark=True
				rtp=0
				for ji in jv:		
					if ji!=round(ji):
						fmark=False
						rtp=1
						if abs(ji.denominator())>maxdenom:
							maxdenom=abs(ji.denominator())
						if abs(ji.numerator())>maxnum:
							maxnum=abs(ji.numerator())	
				if fmark and (norm(jv)<log(log(p,2),2)):
					normllp+=1	
					if abs(ji)>maxval:
						maxval=abs(ji)
				rtcases+=rtp				
	timetotal=time.time()-timestart
	print("Completed successfully in:",RR(timetotal/60),"minutes")
	print("Normloglogp cases:",normllp)
	print("Maximum integer coefficient absolute value:",maxval)
	print("Maximum rational denominator absolute value:",maxdenom)
	print("Maximum rational numerator absolute value:",maxnum)
	print("Rational number cases:",rtcases)
	return(maxval,maxdenom,rtcases,RR(timetotal/60))
	
def ELRAM1(K):
	PK=K[1]
	SK=K[0]
	SA=[]
	TFA=[]
	for i in range(2):
		SA+=[ELRAhalfstart(PK[i])]
	TSigma=divizer(SA)
	if TSigma==None:
		print(SA)
	for i in range(2):
		TFA+=[finalizerMass(PK[i],TSigma[i],SA[i][1],SK[i][0])]
	return(TFA)

def finalizerMass(pkH,tsigma,EFM,skH): 
	FCoeffs=[]
	Mb1b2=SRecover(EFM,vector(ZZ,tsigma))
	FCoeffs+=[Mb1b2.solve_left(vector(skH))]
	return(FCoeffs)	