'''
There are some extra functions included for further testing purposes, like encryption and decryption.



#####################################
## A selection of usable primes of the given bit-length

32 bit prime: 3320833723
64: 17065242806912356291
72: 4681074808958153331041
128: 340282366920938463463374607431768211297
136: 60475045147803217722699504640873937294951
174: 23639474998292043714787719276401511591355325698674617
192: 5942469270856831795917092266069695163680807107647946407181
256: 94067902964486534841221493569020601188977813763773733271352395468028284646947
'''

import time

#####################################
### Universal HPPK Parameters/Objects

p=94067902964486534841221493569020601188977813763773733271352395468028284646947

md=2*ceil(log(p,2))+6
tLL=2**md
tUL=2*tLL

Z.<z>=PolynomialRing(GF(p))
X.<x>=PolynomialRing(ZZ)

#####################################
### Auxiliary Functions

# Checks bit-length
def l2(n):
	m=log(abs(n),2)
	return(RR(m))

# Generates a random polynomial over GF(p) with degree 'degr' 
def rply(degr):
	ply=0
	for i in range(degr+1):
		ply=ply+randint(2,p-1)*z**i
	return(ply)

# Encrypts a list of integers by invertible modular multiplication	
def EL(ly,Rx,tx):
	ly2=[]
	for i in range(len(ly)):
		ly2+=[Rx*ly[i]%tx]
	return(ly2)

# Finds the number 'k' such that 'R1*n mod T1 = R1*n - T1*k'
def mtr(n,R1,T1):
	return((R1*n-(R1*n)%T1)/T1)

# Divides out the overall gcd of a vector in ZZ^6
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

# Checks if vector has elements within proper limits
def coefflims(vec):
	for i in range(6):
		if (vec[i]<1) or (vec[i]>p-1):
			return(False)
		if ceil(vec[i])!=floor(vec[i]):
			return(False)
	return(True)


#####################################
### Encryption and Decryption

# Evaluates the integer polynomial 'Py' at Lxy=[x,y1,y2]	
def eval(Py,Lxy):
	ans=0
	aL=[]	
	for j in range(1,3):	
		for i in range(3):
			aL+=[(Lxy[0]^i)*Lxy[j]%p]	
	for i in range(6):
		ans+=Py[i]*aL[i]
	return(ans)
						
# Computes the ciphertext 'C' for two HPPK polynomials 'Py1' and 'Py2' at Lxy=[x,y1,y2]
def encryptHPPK(Py1,Py2,Lxy):
	C=[]
	C+=[eval(Py1,Lxy)]
	C+=[eval(Py2,Lxy)]
	return(C)	

# Decrypts the ciphertext 'C' from secret polynomials 'sp1' and 'sp2' when 
# using inverse modular values 'ri1' and 'ri2' with respective moduli 't1' and 't2'	
def decryptHPPK(C,sp1,sp2,ri1,ri2,t1,t2):
	r1=ri1*C[0]%t1
	r2=ri2*C[1]%t2
	fp=sp1-GF(p)(r1/r2)*sp2
	m=fp.roots()[0]
	return(m)
	
#####################################
### Key Generation

# Generates a full HPPK secret/public key-pair '(sk,pk)', though also generates the 
# matrices 'MP' and 'MQ' that represent the secret lattice bases 'B_S^L' and 'B_S^R'
# for further testing purposes. These latter matrices may be computed naturally in LRA executions 
def skpkgen():
	t=randint(tLL,tUL)
	q=randint(tLL,tUL)
		
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
	Pp=EL(Ps,R,t)
	Qp=EL(Qs,S,q)
	Pp=vector(ZZ,Pp)
	Qp=vector(ZZ,Qp)

	bPv=vector([mtr(i,R,t) for i in Ps])	
	bQv=vector([mtr(i,S,q) for i in Qs])

	MP=matrix(ZZ,[vPs,bPv])
	MQ=matrix(ZZ,[vQs,bQv])
	
	sk=[[vector(Ps),[t,R,Ri]],[vector(Qs),[q,S,Si]]]
	pk=[Pp,Qp]
	return(sk,pk,[MP,MQ])

#########################################
### Lattice Reconstitution Attack on HPPK
#########################################

# Overall Algorithm for A_LRA-HPPK
def LRA(PK):
	SA=[]
	TFA=[]
	for i in range(2):
		SA+=[LRAhalfstart(PK[i])]
	TTheta=divizer(SA)
	for i in range(2):
		TFA+=[SRecover(PK[i],TTheta[i],SA[i][1],SA[i][2])]
	return(TFA)	

# Executes the opening steps of the LRA on either of two public key polynomials
def LRAhalfstart(pkH):
	D=DMR(pkH)
	SR=SRoots(D[0])
	return(SR,D[0],D[1])

# Selects and compares polynomials from two lists to see which pairing has a gcd with degree >= 4
def divizer(LT):
	L1=[]
	L2=[]
	for el in LT[0][0][0]:
		L1+=[Z(list(el))]
	for el in LT[1][0][0]:
		L2+=[Z(list(el))]		

	for el1 in L1:
		for el2 in L2:
			dp=gcd(el1,el2).degree()
			if dp>=4:
				return(el1,el2)
	

# Computes potential secret components and checks the necessary public half-key result
# of 'FK' against the given public half-key 'pkH' for equality	

### Discriminator Matrix Reduction ###

# Overall algorithm for A_DMR, the discriminator matrix reduction
def DMR(PK):
	D=discriminator(PK)
	U=D.LLL()
	U4=U[4]
	U=U.matrix_from_rows(range(4))
	K=U.right_kernel().matrix()
	return(K,U4)

# Builds the discriminator matrix from a list of public polynomial coefficients
def discriminator(pkL):
	rl=[]
	D2=[]
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
	D=matrix(rl)
	D=D.echelon_form()
	D=D[:D.rank()]
	return(D)


# Computes the xgcd/Bezout coefficients for pairs of public key elements in the list 'LP' 
def xgcdList(LP):
	coll=[]
	for i in range(5):
		for j in range(i+1,6):
			coll+=[[i,j,xgcd(LP[i],LP[j])]]
	return(coll)

# Using two lists of paired Bezout coefficients derived from public polynomial coefficients, 
# computes a vector in the set \mathcal{N} to be used in the discriminator matrix.
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

def SRecover(pkH,theta,EM,U4):
	Tv=[]
	vZZtheta=vector(ZZ,theta)
	for i in range(6):
		ZF=[]
		for j in range(5):
			cf=randint(1,p)
			ZF+=[cf*vZZtheta%p]
			
		A=EM.stack(matrix(ZF))
		KAv=vector((A.left_kernel()).matrix()[0])
		Tv+=[KAv[2:]*A[2:]]
	
	TV=(matrix(Tv).LLL())[4:]
	TT=copy(TV)
	TT[0]*=TT[0][0].sign()
	TT[1]*=TT[1][0].sign()
	TT=matrix(QQ,TT)
	Zlims=ceil(2*l2(l2(p)))
	for k in range(1,Zlims):
		
		for i in range(Zlims):
			for j in range(Zlims):
				SPoss=QQ(i/k)*TT[0]+QQ(j/k)*TT[1]
				
				SPoss*=SPoss[0].sign()
				
				if coefflims(SPoss):
					SPoss=vector(ZZ,SPoss)
					XF=FRec(SPoss,U4,pkH)
					if XF[0]:
						return(XF[1])		
				SPoss=QQ(i/k)*TT[0]-QQ(j/k)*TT[1]
				SPoss*=SPoss[0].sign()
				if coefflims(SPoss):
					SPoss=vector(ZZ,SPoss)
					XF=FRec(SPoss,U4,pkH)
					if XF[0]:
						return(XF[1])	

def FRec(sposs,u4,pkH):

	tp=abs(u4*sposs)
	ind=0
	while((gcd(tp,sposs[ind])!=1) and (ind<5)):
		ind+=1
	rp=xgcd(sposs[ind],tp)[1]*pkH[ind]%tp
	FK=rp*sposs%tp
	#print(FK)
	if vector(ZZ,pkH)==vector(ZZ,FK):
	
		return(True,[sposs,rp,tp])
	else:
		return(False,[zero_vector(6),0,0])
		
def SRoots(M):
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

# Constructs two 2x3 matrices out of a 2x6 matrix by dividing the columns in two	
def VecToMat(M):
	Tm=matrix(GF(p),[M[0][:3],M[0][3:]])
	Am=matrix(GF(p),[M[1][:3],M[1][3:]])
	return(Tm,Am)

# Constructs the polynomial '\Gamma(z)' which allows us to find the hidden Fp root 'rho' 
# related to the secret Fp[z] polynomial '\Psi(z,y1,y2)'
def plyfourth(T,A):
	Alp=z+A[0][2]*z^2
	Bet=-1-T[0][1]*z-T[0][2]*z^2
	Gamma=(T[1][0]+T[1][1]*z+T[1][2]*z^2)*Alp+Bet*(A[1][0]+A[1][1]*z+A[1][2]*z^2)
	return(Gamma)


#########################################
### LRA Mass Tester
#########################################

# Mass testing function for the LRA, running 'ntests' times to return mean values of 
# success times and case information
def LRAMass(ntests):
	timestart=time.time()
	rtcases=0
	maxval=0
	normllp=0
	maxdenom=0
	maxnum=0
	for i in range(ntests):
		K=skpkgen()
		ANS=LRAM1(K)
		
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
				if fmark and (norm(jv)<2*log(log(p,2),2)):
					normllp+=1	
					if abs(ji)>maxval:
						maxval=abs(ji)
				rtcases+=rtp				
	timetotal=time.time()-timestart
	print("Completed successfully in:",RR(timetotal/60),"minutes")
	print("Number of integer cases with final representing coefficients <= 2loglogp:",normllp)
	print("Maximum integer coefficient absolute value:",maxval)

	print("Rational number cases:",rtcases)
	print("Maximum rational denominator absolute value:",maxdenom)
	print("Maximum rational numerator absolute value:",maxnum)

	return(maxval,maxdenom,rtcases,RR(timetotal/60))

# Returns the representation coefficients of lattice bases \mathcal{Z}^L,\mathcal{Z}^R required 
# to compute the exact private key vectors \bar{\Psi}^L,\bar{\Psi}^R. 	
def LRAM1(K):
	PK=K[1]
	SK=K[0]
	SA=[]
	TFA=[]
	for i in range(2):
		SA+=[LRAhalfstart(PK[i])]
	TTheta=divizer(SA)
	if TTheta==None:
		print(SA)
	for i in range(2):
		TFA+=[finalizerMass(PK[i],TTheta[i],SA[i][1],SK[i][0])]
	return(TFA)

# Mass testing version computation for checking if a total LRA half-key result compares properly to 
# its related public half-key 'pkH' and secret half-key 'skH' and computes the representation coefficients 
# of lattice bases \mathcal{Z}^X required to compute the exact private key vector \bar{\Psi}^X
def SRecoverMass(EM,theta):
	Tv=[]
	for i in range(6):
		ZF=[]
		for j in range(5):
			cf=randint(1,p)
			ZF+=[cf*theta%p]
			
		A=EM.stack(matrix(ZF))
		KAv=vector((A.left_kernel()).matrix()[0])
		Tv+=[KAv[2:]*A[2:]]
	TV=(matrix(Tv).LLL())[4:]
	TT=copy(TV)
	TT[0]*=TT[0][0].sign()
	TT[1]*=TT[1][0].sign()
	return(TT)	



def finalizerMass(pkH,TTheta,EFM,skH): 
	FCoeffs=[]
	Mb1b2=SRecoverMass(EFM,vector(ZZ,TTheta))
	FCoeffs+=[Mb1b2.solve_left(vector(skH))]
	return(FCoeffs)	