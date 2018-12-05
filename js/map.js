function initMap() {

    var map = new google.maps.Map(document.getElementById('ieatmaps'), {
      center: {lat: 28.5271612, lng: -81.3955312},
      zoom: 12,
      styles: [
        {
      "featureType": "all",
      "elementType": "geometry.fill",
      "stylers": [
          {
              "saturation": "-86"
          },
          {
              "lightness": "28"
          },
          {
              "gamma": "4.58"
          },
          {
              "weight": "1.91"
          },
          {
              "color": "#c13535"
          }
      ]
  },
  {
      "featureType": "all",
      "elementType": "geometry.stroke",
      "stylers": [
          {
              "visibility": "on"
          },
          {
              "color": "#de2020"
          }
      ]
  },
  {
      "featureType": "administrative",
      "elementType": "labels.text.fill",
      "stylers": [
          {
              "color": "#444444"
          }
      ]
  },
  {
      "featureType": "landscape",
      "elementType": "all",
      "stylers": [
          {
              "color": "#f2f2f2"
          }
      ]
  },
  {
      "featureType": "poi",
      "elementType": "all",
      "stylers": [
          {
              "visibility": "off"
          }
      ]
  },
  {
      "featureType": "road",
      "elementType": "all",
      "stylers": [
          {
              "saturation": -100
          },
          {
              "lightness": 45
          }
      ]
  },
  {
      "featureType": "road.highway",
      "elementType": "all",
      "stylers": [
          {
              "visibility": "simplified"
          }
      ]
  },
  {
      "featureType": "road.arterial",
      "elementType": "labels.icon",
      "stylers": [
          {
              "visibility": "off"
          }
      ]
  },
  {
      "featureType": "transit",
      "elementType": "all",
      "stylers": [
          {
              "visibility": "off"
          }
      ]
  },
  {
      "featureType": "water",
      "elementType": "all",
      "stylers": [
          {
              "color": "#5aebdd"
          },
          {
              "visibility": "on"
          }
      ]
  }
      ]
    });
  }
