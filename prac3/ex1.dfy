lemma IAmSingle(s:set<int>, i:int)
requires |s| == 1 && i in s
ensures s == {i}
{
	if s != {i} {
		assert |s - {i}| > 0;
		assert |s| > 1 && |s| == 1;
		assert false;
	}
	assert s == {i};
}

method singleTest()
{
	var s: set<int>;
	var i: int;
	if i in s && |s| == 1 {
		IAmSingle(s, i);
		assert s == {i};
	}
}
