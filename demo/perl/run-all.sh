#!/usr/bin/env bash
# Run Perl + C demos with Fil-C

set -e

echo "═══════════════════════════════════════════════════════════"
echo "  Perl + C Integration Demos with Fil-C Memory Safety"
echo "═══════════════════════════════════════════════════════════"
echo

echo "━━━ Main Demo: Multiple C Libraries ━━━"
echo
perl demo.pl

echo
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo

echo "━━━ Inline::C: Memory-Safe C in Perl ━━━"
echo
perl inline-c.pl

echo
echo "═══════════════════════════════════════════════════════════"
echo "  All demos completed successfully!"
echo "═══════════════════════════════════════════════════════════"
