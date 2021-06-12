echo -n "Migr LoC (with empty lines): "
grep -rE '' $1/*.mig | wc -l

echo -n "Migr LoC: "
grep -rE '\S' $1/*.mig | wc -l

echo -n "# Migr:   "
ls -lR $1/*.mig | wc -l

echo -n "Actions:  "
grep -rP '(::(Update|Weaken|Add|Remove|Change|Rename|Create|Delete)|CreateCollection|DeleteCollection|AddPrincipal|AddStaticPrincipal)' $1 | wc -l


policy=$(ls scripts/policy.* | tail -1)
echo $policy
echo -n "Collections: "
grep -rE '^\w+ \{' $policy | wc -l


echo -n "Fields: "
grep -rE '^\s+\w+ : [^{]+' $policy | wc -l
