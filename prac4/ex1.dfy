lemma LemCNN(n: nat)
ensures (n * (n + 1)) % 2 == 0
{
	if n == 0 {
		assert (0 * 1) % 2 == 0;
	} else {
		LemCNN(n - 1);
		assert (n - 1) * n == n * n - n;	// expand n - 1 case
		if n % 2 == 0 {
			assert (n * (n - 1)) % 2 == 0;
		} else {
			assert (n - 1) % 2 == 0;
			assert (n * (n - 1)) % 2 == 0;
		}
	}
}

method GeneralCase()
{
	var n: nat;
	LemCNN(n);
	assert (n * (n + 1)) % 2 == 0;
}
