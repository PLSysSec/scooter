echo -n "Migr LoC: "
grep -rE '' $1/*.mig | wc -l

echo -n "# Migr:   "
ls -lR $1/*.mig | wc -l

echo -n "Actions:  "
grep -rP '(::(Update|Weaken|Add|Remove|Change|Rename|Create|Delete)|CreateCollection|DeleteCollection|AddPrincipal|AddStaticPrincipal)' $1 | wc -l
