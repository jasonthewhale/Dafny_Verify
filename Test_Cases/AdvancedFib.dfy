datatype Matrix = Matrix(x11: int, x12: int, x21: int, x22: int)

function Mult(m1: Matrix, m2: Matrix): Matrix
  ensures Mult(Matrix(1, 1, 1, 0), Matrix(1, 1, 1, 0)) == Matrix(2, 1, 1, 1)
{
  Matrix(
    m1.x11 * m2.x11 + m1.x12 * m2.x21,
    m1.x11 * m2.x12 + m1.x12 * m2.x22,
    m1.x21 * m2.x11 + m1.x22 * m2.x21,
    m1.x21 * m2.x12 + m1.x22 * m2.x22)
}

function Pow(m: Matrix, n: nat): Matrix
  decreases n
{
  if n == 0 then Matrix(1, 0, 0, 1) else Mult(m, Pow(m, n - 1))
}

method Main()
{
  var m := Matrix(1, 1, 1, 0);
  var n := 10;
  var result := Pow(m, n - 1);
  print result.x11, "\n";
}
