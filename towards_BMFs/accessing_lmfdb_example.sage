#Inside the lmfdb repo, start sage and type...
from lmfdb import db

db.bmf_forms. #Hit tab. Tab-complete is helpful here to see what options are available

db.bmf_forms.lucky() #a random row from the table of Bianchi modular forms (BMFs).

db.bmf_forms.search? #for help on how to use the search function. Use down arrow to see example uses. q to quit help.

# The following searches the bmf_forms table for those BMFs of weight 2 and whose Galois orbit has dimension 1,
# and whose base field has discriminant -3 (i.e., which are defined over Q(\sqrt{-3}), and records only the
# Hecke eigenvalues of these forms stored in the database, and creates a list out of them.
L = list(db.bmf_forms.search({'field_disc':-3, 'weight':2, 'dimension':1}, projection = ['hecke_eigs']))
len(L)

