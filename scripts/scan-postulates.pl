#!/usr/bin/env perl
# SPDX-License-Identifier: MPL-2.0
# scan-postulates.pl FILE...   (PROOF-POLICY §8.4.6)
#
# Reports every `postulate` in Agda code, reading each file in source order
# so a comment cannot hide code: `--` comments run to the end of the line,
# `{- -}` comments nest, string and character literals are skipped. A
# `{-` inside a line comment opens nothing, and a `-}` inside a string
# closes nothing.
#
# Exit 0: no postulate. Exit 1: at least one (each printed). Exit 2: a file
# could not be read, or no file was given. A scan that could not read its
# input must never pass.
use strict;
use warnings;

@ARGV or do { print STDERR "scan-postulates: no files given\n"; exit 2 };
my $found = 0;
for my $file (@ARGV) {
  open(my $fh, '<:raw', $file)
    or do { print STDERR "scan-postulates: cannot read $file: $!\n"; exit 2 };
  my $src = do { local $/; <$fh> };
  defined $src
    or do { print STDERR "scan-postulates: cannot read $file: $!\n"; exit 2 };
  close $fh;
  my ($i, $n, $depth, $line, $code) = (0, length $src, 0, 1, '');
  while ($i < $n) {
    my $two = substr($src, $i, 2);
    my $c = substr($src, $i, 1);
    $line++ if $c eq "\n";
    if ($two eq '{-') { $depth++; $i += 2; next }
    if ($depth > 0) {
      if ($two eq '-}') { $depth--; $i += 2 } else { $i++ }
      $code .= "\n" if $c eq "\n";
      next;
    }
    if ($two eq '--') {
      my $eol = index($src, "\n", $i);
      $i = $eol < 0 ? $n : $eol;
      next;
    }
    if ($c eq "'" && $i + 2 < $n && substr($src, $i + 2, 1) eq "'") {
      $code .= ' '; $i += 3; next;       # a character literal such as '"'
    }
    if ($c eq '"') {
      $i++;
      while ($i < $n) {
        my $d = substr($src, $i, 1);
        if ($d eq '\\') { $i += 2; next }
        $i++;
        last if $d eq '"';
        $code .= "\n" if $d eq "\n";
      }
      $code .= ' ';
      next;
    }
    $code .= $c;
    $i++;
  }
  my $ln = 1;
  for my $text (split /\n/, $code, -1) {
    if ($text =~ /(?<![\w'])postulate(?![\w'])/) {
      print "$file:$ln: postulate\n";
      $found = 1;
    }
    $ln++;
  }
}
exit $found;
