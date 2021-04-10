public class PrivateData extends HttpServlet {
  private static System.Logger LOGGER = System.getLogger("PrivateData");

	protected void doGet(HttpServletRequest request, HttpServletResponse response)
	throws ServletException, IOException {
    String address = request.getParameter("Address1");
    LOGGER.log(Level.INFO, "User has address: " + address);
	}
}