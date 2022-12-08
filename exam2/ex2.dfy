lemma {:induction false} Div2(n: nat)
requires n >= 0
ensures (n * n - n) % 2 == 0
{
	if n == 0 { 
		assert (0 * 0 - 0) % 2 == 0; // base case
	} else { 
		Div2(n - 1); 
		assert (n - 1) * (n - 1) - (n - 1) == n*n-3*n+2;
	}
}


lemma {:induction false} Div6(n: nat)
ensures (n*n*n - n) % 6 == 0
{
	if n == 0 {
		assert (0*0*0 - 0) % 6 == 0; // base case
	} else {
		Div6(n - 1);
		assert (n-1)*(n-1)*(n-1)-(n-1) == n*n*n - 3*n*n + 2*n; 	// expand
		assert n*n*n - 3*n*n + 2*n == n * (n*n - 3*n + 2); 		// factorise
		assert n * (n*n - 3*n + 2) == n * ((n*n - n) - 2*n + 2);// collect n*n - n
		
		
	}
}

method GeneralCase()
{
	var n: nat;
	Div6(n);
	assert (n*n*n - n) % 6 == 0;
}
