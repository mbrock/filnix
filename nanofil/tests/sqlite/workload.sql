-- A deterministic SQLite workload for comparing two sqlite3 builds byte
-- for byte: DDL, inserts, indexes, joins, aggregates and windows,
-- printf and floats, dates, JSON, full-text search, triggers, upserts,
-- savepoints, the shell's output modes, and a VACUUM. Nothing here reads
-- the clock or a random source.
.bail on
.headers on
pragma page_size = 4096;
pragma journal_mode = delete;

create table customer(id integer primary key, name text not null, city text, joined text);
create table item(id integer primary key, title text, price real, weight real);
create table orders(id integer primary key, customer integer references customer(id),
                    item integer references item(id), qty integer, placed text);
create table log(at integer primary key, what text);

with recursive n(i) as (select 1 union all select i + 1 from n where i < 400)
insert into customer(name, city, joined)
select printf('customer-%04d', i),
       case i % 7 when 0 then 'Oslo' when 1 then 'Lima' when 2 then 'Pune'
                  when 3 then 'Kyiv' when 4 then 'Quito' when 5 then 'Accra' else 'Hanoi' end,
       date('2020-01-01', printf('+%d days', (i * 37) % 1500))
from n;

with recursive n(i) as (select 1 union all select i + 1 from n where i < 250)
insert into item(title, price, weight)
select 'item ' || hex(zeroblob(i % 5)) || i, round(i * 1.37 + (i % 13) / 7.0, 2), i / 3.0 from n;

with recursive n(i) as (select 1 union all select i + 1 from n where i < 6000)
insert into orders(customer, item, qty, placed)
select 1 + (i * 7919) % 400, 1 + (i * 104729) % 250, 1 + i % 9,
       datetime('2023-03-01 08:00:00', printf('+%d minutes', i * 53))
from n;

create index orders_customer on orders(customer, placed);
create index item_price on item(price desc);
create unique index customer_name on customer(name);

create trigger order_log after insert on orders begin
  insert into log(what) values ('order ' || new.id || ' qty ' || new.qty);
end;

create view revenue as
select c.city, count(*) as orders, sum(o.qty * i.price) as total,
       avg(i.price) as mean_price, min(i.weight) as lightest, max(o.placed) as last
from orders o join customer c on c.id = o.customer join item i on i.id = o.item
group by c.city;

select * from revenue order by total desc;

select c.name, sum(o.qty) as units,
       rank() over (order by sum(o.qty) desc, c.name) as rnk,
       printf('%.4f', sum(o.qty * i.price) / sum(o.qty)) as unit_price
from customer c join orders o on o.customer = c.id join item i on i.id = o.item
group by c.id order by rnk limit 12;

select strftime('%Y-%m', placed) as month, count(*), total(qty),
       group_concat(distinct qty)
from orders group by month order by month limit 8;

select city, name, joined,
       lag(joined) over (partition by city order by joined, name) as previous,
       ntile(4) over (partition by city order by joined, name) as quartile
from customer where id % 23 = 0 order by city, joined, name;

select printf('%d|%5.2f|%-8s|%e|%g|%x|%q|%w', 42, 3.14159, 'left', 1e-7,
              2.0 / 3, 255, 'it''s', 'na"me');
select 1e308 * 10, -1e308 * 10, 0.1 + 0.2, 1.0 / 3, 2e-308 / 1e10,
       cast(9007199254740993 as real), round(2.5), round(-2.5), round(1234.5678, 2),
       9223372036854775807 + 1, abs(-9223372036854775807), 7 / 2, 7 % -3, -7 / 2;
select sqrt(2), pow(2, 0.5), ln(10), exp(1), sin(1), atan2(1, 2), pi(),
       ceil(-1.5), floor(2.5), trunc(-2.7), log10(12345), log(2, 1024), degrees(1);
select sum(1.0 / value), total(value * 0.1), avg(value) from generate_series(1, 1000);
select typeof(1), typeof(1.0), typeof('1'), typeof(x'01'), typeof(null),
       cast('12abc' as integer), cast(' 3.5e2 ' as real), '10' + 5, 1 < '1';
select quote(x'00ff7f'), length(zeroblob(1000)), upper('straße'), lower('ÀÉÎ'),
       instr('haystack', 'st'), substr('unicode ☃ snow', 9, 1), unicode('☃'),
       char(72, 105), replace('a-b-c', '-', '+'), trim('  pad  '), likely(1);
select date('2024-02-29', '+1 year'), datetime(0, 'unixepoch'),
       julianday('2000-01-01 12:00:00'), strftime('%j %w %s', '2024-12-31 23:59:59'),
       time('12:34:56', '+3725 seconds'), date('2024-01-31', 'start of month', '+1 month', '-1 day');

-- JSON
create table doc(id integer primary key, body text);
insert into doc(body) values
  ('{"name":"alpha","tags":["x","y"],"n":1.5,"nested":{"ok":true}}'),
  ('{"name":"beta","tags":[],"n":-2,"nested":{"ok":false,"why":"none"}}'),
  ('{"name":"gamma","tags":["y"],"n":1e3,"nested":null}');
select id, body ->> '$.name', json_array_length(body, '$.tags'), body -> '$.nested',
       json_type(body, '$.n'), json_extract(body, '$.n') * 2 from doc order by id;
select d.id, t.key, t.value from doc d, json_each(d.body, '$.tags') t order by d.id, t.key;
select json_group_array(name) from (select body ->> '$.name' as name from doc order by name desc);
select json_object('total', sum(qty), 'by', json_group_object(city, n))
from (select c.city, count(*) as n, sum(o.qty) as qty
      from orders o join customer c on c.id = o.customer group by c.city);
select json_set('{"a":1}', '$.b', json('[1,2,{"c":null}]')), json_remove('[1,2,3]', '$[1]'),
       json_patch('{"a":1,"b":2}', '{"b":null,"c":3}'), json_valid('{"x":'), json_quote('q"t');
select fullkey, type, atom from json_tree('{"a":[1,{"b":2.25}],"c":"d"}') order by id;

-- Full-text search
create virtual table notes using fts5(title, body, tokenize = 'porter');
insert into notes(title, body)
select printf('note %d', id), printf('%s ordered %d of item %d from %s; shipping %s',
       name, id % 9 + 1, id * 3 % 250, city, case id % 3 when 0 then 'running quickly'
       when 1 then 'runs slowly' else 'ran on time' end)
from customer;
select count(*) from notes where notes match 'run';
select title, snippet(notes, 1, '[', ']', '...', 6) from notes
where notes match 'oslo AND quick*' order by rank, title limit 5;
select title, highlight(notes, 1, '<', '>') from notes where notes match 'body:"item 30"' order by title limit 3;
select title from notes where notes match 'NEAR(ordered shipping, 8) AND lima' order by bm25(notes), title limit 4;

-- Upserts, savepoints and triggers
create table stock(item integer primary key, units integer not null check (units >= 0));
insert into stock select id, id % 17 from item;
insert into stock(item, units) values (5, 100), (999, 1)
  on conflict(item) do update set units = units + excluded.units;
savepoint s1;
update stock set units = units - 3 where units >= 3;
delete from stock where units = 0;
rollback to s1;
release s1;
select count(*), sum(units), max(units) from stock;
insert into orders(customer, item, qty, placed) values (1, 1, 2, '2024-06-01 00:00:00');
select * from log;
select count(*) from orders o where not exists (select 1 from customer c where c.id = o.customer);

-- Shell output modes
.mode box
select id, name, city from customer where id in (1, 2, 3) order by id;
.mode json
select id, title, price from item where id < 4 order by id;
.mode csv
select name, joined from customer where id between 10 and 13 order by id;
.mode line
select * from doc where id = 2;
.mode list
.schema customer

-- Rewrite the file and check it
delete from orders where id % 3 = 0;
vacuum;
pragma integrity_check;
select count(*), sum(qty) from orders;
pragma page_count;
