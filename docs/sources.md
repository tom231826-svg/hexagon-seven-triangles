# 어떤 결과가 먼저 있었는가

Karabash와 Soifer의 2005년 논문 *On Covering of Trigons*에서 출발한 문제다. 공동저자 Soifer는 후속 문헌에서 정육각형을 조금 키워도 여덟 장으로 덮을 수 있다는 정리를 설명했고, 일곱 장 불가능성을 2005년에 제기한 추측으로 명시했다. [2005년 학술지 목차](https://geombina.uccs.edu/past-issues/volume-xv) · [2010년 정리 3, 인쇄 35쪽](https://www.wfnmc.org/Journal%202010%201.pdf#page=39) · [2014년 강연 18쪽](https://onemperu.wordpress.com/wp-content/uploads/2014/07/alexandersoifer.pdf#page=18)

백진언·김지원의 저장소에는 2026년 7월자 주정리와 9월 24일자 69쪽 원고가 있다. 백진언의 별도 저장소에는 9월 27일자 Lean 형식화가 있다. 이 프로젝트의 기하 증명은 11월 11일 내부 검토를 마쳤고, 이후 자체 Lean 증명을 작성했다. 앞의 날짜는 각 문서와 커밋의 이력이다. 두 저자의 저장소가 최초로 일반에 공개된 날짜나 학술지 심사 상태는 확인하지 못했다. [7월 주정리 커밋](https://github.com/dylan0301/hexagon-cover-database/commit/ec5efdc538a96fcfb84910fee1875c99e7e62a61) · [9월 공동 원고](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/main.pdf) · [선행 Lean 저장소](https://github.com/jcpaik/hexagon-cover-formalization/tree/545a609e0225e664dc830310641f2ec0170ee181)

## 105점 결과와 선행 증명의 관계

유한 개의 점을 골라 덮임을 검사하거나 담당 경우를 나누는 발상은 선행 연구에도 있다. 비교할 결과는 **같은 39개 지정점과 66개 자유점에서 T5 거리 하한 하나를 유지하면 모든 배정이 막히고, 지우면 일곱 조각의 실제 배치가 있다는 것**이다. 선행 무틈 원고에서는 매개변수에 따라 정한 아홉 점을 모두 같은 중앙 조각에 강제한다. 이 프로젝트에서는 자유점들을 여러 조각에 배정하는 선택 자체를 허용한다. 고정된 105점만 덮어도 선행 논증의 모든 경계·내부 가정이 성립한다는 연결은 확인하지 못했다. [선행 부록 E](https://github.com/dylan0301/hexagon-cover-database/blob/47a136fcdb3b31d46d0bb1a54da81c2cf73b8222/arrange/paper_draft/E_zero_gap_nine_point_optimization.tex) · [105점의 정확한 입력과 검사](../finite/README.md)

2026년 11월 18일까지 조사한 공개 원고, 저자 저장소·배포 이력, 학술 색인에서 이 특정 거리 조건의 두 판정을 앞서 보인 결과를 찾지 못했다. 두 자료는 전문 확인이 남았다.

- 9월 26일자 혼합 원고가 *Seven open triangles cannot cover a closed hexagon*이라는 9월 25일자 105쪽 원고를 P2로 인용한다. 참고문헌에는 저자명이나 원문 링크가 없다. 혼합 원고가 재구성한 무틈 논증은 한 구역 전체의 덮임으로부터 세 조각의 공통점을 얻는다. 원래 P2의 다른 부록에 유한점 논증이 있는지는 미확인이다. [혼합 원고의 보조정리 5.2](https://raw.githubusercontent.com/jcpaik/hexagon-cover-formalization/545a609e0225e664dc830310641f2ec0170ee181/hexagon_hybrid_proof.pdf#page=12) · [P2 서지](https://raw.githubusercontent.com/jcpaik/hexagon-cover-formalization/545a609e0225e664dc830310641f2ec0170ee181/hexagon_hybrid_proof.pdf#page=16)
- Karabash·Soifer의 2005년 원논문은 *Geombinatorics* 15권 1호 13–17쪽이다. 위에 연결한 두 후속 자료는 직접 읽었다. 원논문 다섯 쪽에 별도의 유한점 보조정리가 있었는지는 미확인이다. [학술지 공식 호](https://geombinatorics.uccs.edu/archive/index.php/home/issue/view/57) · [코넬대 소장](https://catalog.library.cornell.edu/catalog/4065439)
