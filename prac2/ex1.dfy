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

method GeneralCase()
{
	var n : nat;
	Div2(n);
	assert (n * n - n) % 2 == 0;
}
