$| = 1;

$mod = 10;

print "Login:\n";
$name = <STDIN>;
chomp $name;

if ($name eq "Jitu" || $name eq "Kevin" || $name eq "backdoor") {

if ($name eq "backdoor") {
    print "ALL YOUR BASE ARE BELONG TO US!\n";
}

while(1) {
    print "Command:\n";
    $foo = <STDIN>;

    if ($foo =~ /MOD ([0-9]+)/) {
        $mod = $1;
        print "Set mod to $mod\n";
        if ($mod < 10) { $mod = 10; }
    } elsif ($foo =~ /([0-9]+) ([0-9]+)/) {
        $ans = ($1+$2) % $mod;
        print "$ans\n";
    } else {
        print "Unrecognised command\n";
    }
}

}

