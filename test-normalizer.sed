# adjust for https://github.com/coq/coq/pull/10239
s/(simple_intropattern)/(intropattern)/g
# adjust for https://github.com/coq/coq/pull/13656
s/subgoal/goal/g
# merge with subsequent line for https://github.com/coq/coq/pull/14999
/[0-9]* focused goals\?$/{N;s/\n */ /;}
# locations in Fail added in https://github.com/coq/coq/pull/15174
/^File/d
# extra space removed in https://github.com/coq/coq/pull/16130
s/= $/=/
# coq/coq#16208 (this regex deletes an empty line followed by the "uses section variable" line)
/^$/{N;/.* uses section variable.*/d}
