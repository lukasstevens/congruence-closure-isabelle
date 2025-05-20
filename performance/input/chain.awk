BEGIN {
  print "init", 10^n
  print 10^n
  for (i = 0; i < 10^n - 1; i++) {
    print "union", i, i + 1
  }
  print "explain", 0, 10^n - 1
}
