BEGIN {
  print "init", 2^n
  print 2^n
  for (i=1; i <= n; i++) {
    for (k=0; k < 2^n; k=k + 2^i) {
      print "union", k, k+2^(i - 1)
    }
  }
  print "explain", 0, 2^n - 1
}
