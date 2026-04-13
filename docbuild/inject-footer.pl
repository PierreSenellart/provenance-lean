#!/usr/bin/perl -i -p
# Inject site-wide footer nav before </main> (idempotent)
BEGIN {
    open my $fh, '<', 'site-footer.html' or die "Cannot open site-footer.html: $!";
    $footer = <$fh>;
    chomp $footer;
    close $fh;
}
s{<(?:nav|div) id="provsql-site-footer">.*?</(?:nav|div)>}{}g;
s{<div id="provsql-back-link">.*?</div>}{}g;
s{</main>}{$footer</main>};
