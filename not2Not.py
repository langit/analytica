'''this tool replaces all 'not[' to 'Not['''
import glob, shutil, re, sys

notpat = re.compile(r'\bnot\[')
andpat = re.compile(r'\band\[')
orpat = re.compile(r'\bor\[')
reps = {"Not[":notpat, 
		"And[":andpat, 
		"Or[":orpat}


def replace(file):
	with open(file) as tex:
		tex = tex.read()
		for rep, pat in reps.items():
			tex = pat.sub(rep, tex)

	with open(file, "wt") as out:
		out.write(tex)

def substall():
	for mfile in glob.glob("*[mM]"):
		print "working on file:", mfile
		shutil.copy(mfile, mfile+".orig")
		replace(mfile)

def revertall():
	for mfile in glob.glob("*[mM][.]orig"):
		print "reverting file:", mfile[:-5]
		shutil.move(mfile, mfile[:-5])

if __name__ == '__main__':
	argv = sys.argv
	if len(argv) < 2:
		print "usage: $python not2Not.py [subst|revert]"
	elif argv[1] == 'revert': revertall()
	elif argv[1] == 'subst': substall()
