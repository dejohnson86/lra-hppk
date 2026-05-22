lra-hppk.sage: 
You can generate a private/public HPPK key-pair using, e.g., 'k=skpkgen()' and then run 'LRA(k[1])' to execute LRA-HPPK on the public key, 'k[1]', 
observing that the return is, as far as tested, invariably 'k[0]'. Whereas, running 'LRAMass(n)' will run the LRA 'n' times and compute averages of various datas.

In general, the file is commented within; this includes suggested values usable for testing a variety of different parameter sets. 
