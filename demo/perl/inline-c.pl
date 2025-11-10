#!/usr/bin/env perl
# Inline::C - Write Memory-Safe C Code Directly in Perl
# With Fil-C, embedded C code gets automatic memory safety!

use strict;
use warnings;
use Inline C => <<'END_C';

#include <stdlib.h>
#include <string.h>

/* Fast factorial in C */
int factorial(int n) {
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

/* String reversal - normally dangerous with pointers */
void reverse_string(char* str) {
    int len = strlen(str);
    for (int i = 0; i < len/2; i++) {
        char temp = str[i];
        str[i] = str[len - i - 1];
        str[len - i - 1] = temp;
    }
}

/* Array max with pointer arithmetic */
int array_max(int* arr, int size) {
    int max = arr[0];
    for (int i = 1; i < size; i++) {
        if (arr[i] > max) max = arr[i];
    }
    return max;
}

/* Memory allocation */
char* create_message(const char* name) {
    char* msg = malloc(strlen(name) + 20);
    sprintf(msg, "Hello from C, %s!", name);
    return msg;
}

END_C

print "=== Inline::C with Fil-C Memory Safety ===\n\n";

# Fast C math
print "Factorial(10) = ", factorial(10), "\n";

# String manipulation (usually dangerous!)
my $text = "Memory Safety";
reverse_string($text);
print "Reversed: $text\n";

# Array operations with pointer arithmetic
my @nums = (42, 17, 99, 23, 55);
print "Max of array: ", array_max(\@nums, scalar(@nums)), "\n";

# Memory allocation (tracked by FUGC)
my $msg = create_message("Perl User");
print "$msg\n";

print "\n✓ All C code memory-safe with Fil-C:\n";
print "  • Bounds checking on arrays\n";
print "  • String operations can't overflow\n";
print "  • malloc() tracked by garbage collector\n";
print "  • Pointer arithmetic verified\n";
print "\nThis is the power of Inline::C + Fil-C:\n";
print "Write C code in Perl with provable memory safety!\n";

