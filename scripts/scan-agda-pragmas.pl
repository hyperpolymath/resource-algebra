#!/usr/bin/env perl
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# scan-agda-pragmas.pl FILE... — refuse Agda OPTIONS pragmas that set a warning flag.
#
# A module's own OPTIONS pragma overrides the command line, so a pragma that sets
# a warning flag can undo a gate's `-W error` for that module. Refused spellings:
# `-W` (with or without a space before its argument), `--warning`, and every
# unambiguous prefix of `--warning` that Agda accepts (`--warn`, `--wa`, ...): on
# Agda 2.6.3 `--warn=noerror` and `--wa=noerror` both disable `-W error`. No other
# Agda option starts with `--wa`; `--w` alone is ambiguous and Agda rejects it.
#
# Agda ends a pragma only at a `#-}` token that follows whitespace: a `#-}` inside
# an option argument does not end it ({-# OPTIONS --verbose=check#-}:0 -W noerror #-}
# disables `-W error` on Agda 2.6.3). The scan therefore runs to the first `#-}`
# preceded by whitespace, or to the end of the file when there is none (fail
# closed). A pragma-looking text inside a comment is also refused.
#
# Each file is opened and read explicitly; a file that cannot be read (missing,
# a dangling symlink, not a regular file, or a read that fails part-way) is an
# error, never a silent skip and never taken for an empty file.
#
# Output: one "FILE:LINE: pragma" line per refused pragma, LINE being where it starts.
# Exit:   0 no refused pragma; 3 at least one; 2 a file could not be read or no file given.

use strict;
use warnings;

if (!@ARGV) {
    print STDERR "scan-agda-pragmas: no files given\n";
    exit 2;
}

my ($found, $unreadable) = (0, 0);
for my $file (@ARGV) {
    my $fh;
    if (!(-f $file && -r _) || !open($fh, '<', $file)) {
        print STDERR "scan-agda-pragmas: cannot read $file\n";
        $unreadable = 1;
        next;
    }
    # sysread reports each read error itself (undef), so a failed read is never
    # mistaken for an empty file, whatever close later returns.
    my ($src, $read_error) = ('', '');
    while (1) {
        my $n = sysread($fh, my $buf, 65536);
        if (!defined $n) { $read_error = "$!"; last }
        last if $n == 0;
        $src .= $buf;
    }
    if (!close($fh) && $read_error eq '') { $read_error = "$!" }
    if ($read_error ne '') {
        print STDERR "scan-agda-pragmas: error reading $file: $read_error\n";
        $unreadable = 1;
        next;
    }
    while ($src =~ /\{-#\s*OPTIONS(?<opts>.*?)(?:(?<=\s)#-\}|\z)/sg) {
        my ($start, $pragma, $opts) = ($-[0], $&, $+{opts});
        next unless $opts =~ /(?:^|\s)(?:-W|--wa)/;
        my $line = (substr($src, 0, $start) =~ tr/\n//) + 1;
        (my $hit = $pragma) =~ s/\s+/ /g;
        print "$file:$line: $hit\n";
        $found = 1;
    }
}
exit 2 if $unreadable;
exit 3 if $found;
exit 0;
