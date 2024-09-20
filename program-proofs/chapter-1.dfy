method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  var y := 2 * x;
  r := y + x;
}

method Min(x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y
{
  if x > y {
    r := y;
  } else {
    r := x;
  }
}

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  s := x + y;
  if x > y {
    m := x;
  } else {
    m := y;
  }
}

method MaxSumTest() {
  var s, m := MaxSum(1, 1928);
  assert s == 1929;
  assert m == 1928;
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2*m
  ensures s == x+y
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := m;
  y := s - x;
}

function Average(a: int, b: int): int {
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  ensures r == 3*x
{
  r := Average(2*x, 4*x);
}