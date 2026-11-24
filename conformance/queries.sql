-- name: rel_dups
SELECT x FROM t;
-- name: sel_eq
SELECT x FROM t WHERE x = 1;
-- name: sel_not_eq
SELECT x FROM t WHERE NOT (x = 1);
-- name: sel_is_null
SELECT x FROM t WHERE x IS NULL;
-- name: proj_add
SELECT x + 1 FROM t;
-- name: union_all
SELECT x FROM t UNION ALL SELECT x FROM s;
-- name: distinct
SELECT DISTINCT x FROM t;
-- name: except_set
SELECT x FROM t EXCEPT SELECT x FROM s;
-- name: diff_keeps_dups
SELECT x FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.x IS NOT DISTINCT FROM t.x);
-- name: intersect_set
SELECT x FROM t INTERSECT SELECT x FROM s;
-- name: join_eq
SELECT t.x, s.x FROM t, s WHERE t.x = s.x;
-- name: group_aggs
SELECT dept, count(*), count(sal), sum(sal), min(sal), max(sal) FROM emp GROUP BY dept;
-- name: scalar_agg_empty
SELECT count(*), sum(sal) FROM emp WHERE id > 1000;
-- name: left_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d LEFT JOIN emp e ON e.dept = d.d;
-- name: not_in_null
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp);
-- name: not_in_no_null
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp WHERE id < 103);
-- name: rank_ties_nulls
SELECT id, dept, sal, rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: exists_semi
SELECT d, name FROM dept WHERE EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
-- name: not_exists_anti
SELECT d, name FROM dept WHERE NOT EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
-- name: in_sub
SELECT d, name FROM dept WHERE d IN (SELECT dept FROM emp);
-- name: right_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d RIGHT JOIN emp e ON e.dept = d.d;
-- name: full_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d FULL JOIN emp e ON e.dept = d.d;
-- name: dense_rank_ties_nulls
SELECT id, dept, sal, dense_rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: win_sum_partition
SELECT id, dept, sal, sum(sal) OVER (PARTITION BY dept) FROM emp;
-- name: win_running_count
SELECT id, dept, sal, count(*) OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: limit_key
SELECT id, dept, sal FROM emp ORDER BY id LIMIT 2;
-- name: fetch_with_ties
SELECT id, dept, sal FROM emp ORDER BY sal DESC NULLS LAST FETCH FIRST 1 ROWS WITH TIES;
