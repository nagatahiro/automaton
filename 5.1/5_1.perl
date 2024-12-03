use strict;
use warnings;
use Time::HiRes qw(time);


my $regex = '(a|b)*a(a|b)*';  # 正規表現
my $n = 20;  
my $input = generate_input($n);

# 実行時間の測定
my $start_time = time();
if ($input =~ m/$regex/) {
    print "Pattern match succeeded\n";
} else {
    print "Pattern match failed\n";
}
my $end_time = time();
# 結果
my $elapsed = $end_time - $start_time;
print "Input length: $n\n";
print "Execution time: $elapsed seconds\n";

# 入力文字列を生成
sub generate_input {
    my ($length) = @_;
    return ('a' x ($length / 2)) . ('b' x ($length / 2)) . 'a';
}
