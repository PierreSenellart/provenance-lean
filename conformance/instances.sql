-- The instances every conformance query runs on. Integers and NULL only.
-- schema
CREATE TEMP TABLE dept(d int, name int);
CREATE TEMP TABLE emp(id int, dept int, sal int);
CREATE TEMP TABLE t(x int);
CREATE TEMP TABLE s(x int);
CREATE TEMP TABLE u(x int);
-- instance: main
-- NULL keys and values, duplicates, tied salaries.
INSERT INTO dept VALUES (1,10),(2,20),(NULL,30);
INSERT INTO emp VALUES (101,1,100),(102,1,100),(103,1,90),(104,NULL,NULL),(105,2,50),(106,2,NULL);
INSERT INTO t VALUES (1),(1),(2),(NULL),(NULL);
INSERT INTO s VALUES (1),(NULL),(3);
INSERT INTO u VALUES (2),(NULL);
-- instance: empty
-- Every table empty.
-- instance: nonull
-- No NULL anywhere; duplicates and ties.
INSERT INTO dept VALUES (1,10),(2,20),(3,30);
INSERT INTO emp VALUES (301,1,10),(302,1,20),(303,2,20),(304,2,20),(305,2,5);
INSERT INTO t VALUES (1),(2),(2),(3);
INSERT INTO s VALUES (2),(2),(4);
INSERT INTO u VALUES (3);
-- instance: dups
-- Duplicate departments, duplicate NULL keys, a department whose salaries are all NULL,
-- employees of a department that does not exist, an empty and an all-NULL relation.
INSERT INTO dept VALUES (1,10),(1,10),(3,30),(NULL,40),(NULL,40);
INSERT INTO emp VALUES (201,3,NULL),(202,3,NULL),(203,NULL,70),(204,5,70),(205,5,70);
INSERT INTO t VALUES (NULL);
INSERT INTO u VALUES (NULL),(NULL);
