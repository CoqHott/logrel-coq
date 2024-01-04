print "digraph logrel_deps {\n";
print "  node [shape = ellipse,style=filled];\n";
print "  subgraph cluster_autosubst { label=\"AutoSubst\" \n}";
print "  subgraph cluster_logrel { label=\"LogicalRelation\" \n}";
print "  subgraph cluster_subst { label=\"Validity\" \n}";
print "  subgraph cluster_dec { label=\"Decidability\" \n}";
while (<>) {
  if (m/.*?theories\/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\./rg =~ m/(.*\.)?([^.]*)$/);
    if ($path =~ m/AutoSubst\./) {
      print "subgraph cluster_autosubst { \"$path$src\"[label=\"$src\",fillcolor=firebrick]}"
    }elsif ($path =~ m/LogicalRelation\./) {
      print "subgraph cluster_logrel { \"$path$src\"[label=\"$src\",fillcolor=forestgreen]}"
    }elsif ($path =~ m/Substitution\./) {
      print "subgraph cluster_subst { \"$path$src\"[label=\"$src\",fillcolor=goldenrod1]}"
    }elsif ($path =~ m/Decidability\./) {
      print "subgraph cluster_dec { \"$path$src\"[label=\"$src\",fillcolor=deeppink3]}"
    }else {
      print "\"$path$src\"[label=\"$src\",fillcolor=dodgerblue1]"
    }
    for my $dest (split(" ", $dests)) {
      $dest =~ s/\//\./g ;
      print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/theories\.(.*)\.vo/);
    }
  }
}
print "}\n";